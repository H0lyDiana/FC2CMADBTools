// ==UserScript==
// @name         FC2CMADBTools
// @namespace    http://tampermonkey.net/
// @version      2.2
// @description  提取7位数字生成对应链接悬浮窗、移除图片模糊、页面自定义翻译、跨页保留番号(?page=N, 换路径/搜索条件自动清空)、无资源折叠(仅当前页)、并发检测与头部进度。
// @author       AI
// @match        https://fc2cmadb.com/*
// @grant        GM_xmlhttpRequest
// @grant        GM_openInTab
// @connect      sukebei.nyaa.si
// @connect      fc2cmadb.com
// @run-at       document-idle
// ==/UserScript==

(function() {
    'use strict';

    // ====================== 全局常量配置区 ======================
    const CONFIG = {
        DEBOUNCE_WAIT: 300,
        FLOAT_WIN_WIDTH: 340,
        FLOAT_WIN_MAX_HEIGHT: 420,
        FLOAT_WIN_ZINDEX: 999999,
        NUMBER_SCAN: /\d{6,7}/g,        // matchAll 内部会克隆，不会污染 lastIndex
        STORAGE_KEY_WIN_POS: 'fc2cmadb_float_pos',
        STORAGE_KEY_THEME: 'fc2cmadb_theme',
        CHECK_CONCURRENCY: 5,           // 每批同时发出的请求数
        CHECK_BATCH_WAIT_MS: 1000,      // 一批全部返回后等待多久再发下一批
        CHECK_TIMEOUT_MS: 10000,        // 单次请求超时，避免卡死整条队列
        BAN_COOLDOWN_MS: 60000,         // 被 429/403 后的冷却时间
        LOCATE_FLASH_MS: 1600,          // 定位覆盖层闪烁时长
        FLUSH_NODE_BUDGET: 220,         // 每帧最多处理的 DOM 节点预算（防长任务卡顿）
        CACHE_SOFT_LIMIT: 800,          // 状态缓存软上限，超出后清理非本页条目
        TIP_DELAY_MS: 450,              // 悬停多久弹出详情
        OPEN_ALL_MAX: 40,               // 一键打开上限，避免标签页风暴
        SESSION_MAX: 2000,              // 跨页会话最多保留多少个番号
        SAVE_DEBOUNCE_MS: 400,          // 会话状态写盘节流
        SCOPE_SETTLE_MS: 1200           // 换列表后的「重建」窗口：这段时间内以扫描结果为准，不做累加
    };

    const translationDict = {
        "ランキング": "排行", "コメントする": "发表评论", "セール": "折扣",
        "コメント": "评论", "お気に入り": "收藏", "女優": "女优",
        "販売者": "作者", "タイトル ID": "标题ID", "人気作品": "人气作品",
        "すべて見る": "查看全部", "テーマ切り替え": "切换主题",
        "ライトモードに切り替える": "白天模式", "ダークモードに切り替える": "黑暗模式",
        "システムテーマを有効にする": "跟随系统设置",
        "旧サイトのアカウントでログインできます。": "可以用旧网站的账号登录。",
        "コメント履歴": "历史评论", "まだコメントはありません": "暂无评论",
        "アカウント": "账户", "ログアウト": "退出登录", "モザイク": "马赛克",
        "販売日": "销售日期", "収録時間": "收录时间", "タグ": "标签",
        "リンク": "关联", "閉じる": "关闭","検索結果": "搜索结果",
        "表示中": "此页显示", "から": "至","件目": " ",
        "、全": "   总计"
    };

    // 翻译词典编译：长词优先 + 单次替换，避免依赖对象键顺序
    const escapeRe = s => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const TRANS_KEYS = Object.keys(translationDict).sort((a, b) => b.length - a.length);
    const TRANS_SOURCE = TRANS_KEYS.map(escapeRe).join('|');
    const TRANS_RE = new RegExp(TRANS_SOURCE, 'g');
    const TRANS_TEST = new RegExp(TRANS_SOURCE);
    const TRANS_MAP = new Map(Object.entries(translationDict));
    const translateString = s => s.replace(TRANS_RE, m => TRANS_MAP.get(m) ?? m);

    const TRANS_ATTRS = new Set(['title', 'alt', 'aria-label', 'placeholder', 'data-tip', 'data-tooltip']);
    const SKIP_TAGS = ['SCRIPT', 'STYLE', 'TEXTAREA', 'NOSCRIPT', 'IFRAME'];
    const isSkippedEl = el => !el || SKIP_TAGS.includes(el.tagName);

    // 番号容器选择器：优先精确匹配，站点改版时降级到宽松匹配
    const STRICT_ID_SELECTORS = [
        'span.absolute.top-0.left-0.text-sm.text-white.bg-gray-800.opacity-80.rounded-tl-lg.px-1',
        'td.w-8\\/10.text-base.font-medium'
    ];
    const FALLBACK_ID_SELECTORS = [
        'span.absolute[class*="bg-gray"]',
        'td.font-medium',
        'td.text-base'
    ];
    const ID_BADGE_SELECTOR = STRICT_ID_SELECTORS.join(',');
    const NUMBER_SCAN_RE = new RegExp(CONFIG.NUMBER_SCAN.source, 'g');

    // 卡片容器判定：用于定位、折叠、翻页追加
    const CARD_SELECTOR = 'article, li, tr, .card, [class*="card"], [class*="item"], [class*="post"], [class*="thumb"], [class*="box"]';

    // 状态 -> 样式类 / 文案映射（集中管理，避免多处 if-else 漂移）
    const STATUS_CLASS = { 'not-found': 'not-found', loading: 'loading', error: 'error', banned: 'banned' };
    const STATUS_TEXT = { 'not-found': '[无资源]', loading: '[检测中]', error: '[网络错误]', banned: '[请求频繁]' };

    let foundNumbers = new Set();         // 全部番号（含前几页带过来的）
    let numIndex = new Map();             // num -> { el: 番号节点, card: 所在卡片 }，仅当前页
    const numPage = new Map();            // num -> 第一次出现在第几页
    let activeScope = '';                 // 当前列表身份：pathname + 除 page 外的查询参数
    let scopeSettleUntil = 0;             // 换列表后的重建窗口截止时间（此期间扫描结果覆盖而非累加）
    let floatWindow = null;
    let observer = null;
    let userClosed = false;               // 用户主动关闭后，不再被自动重绘弹出来
    let hideMode = false;                 // 是否折叠「无资源」卡片
    const hiddenCards = new Map();        // card -> 原始 inline display
    let winDragPos = { left: '', top: '' };

    // 表格行引用缓存：状态更新时直接改节点，不再 querySelectorAll
    const rowRefs = new Map();            // num -> { link, mark, btn }
    let renderedSig = '';                 // 当前已渲染的番号签名，结构不变时只刷状态
    let suppressToolbar = false;          // 批量回填状态时避免重复统计

    // ======= 资源有效性检测核心 =======
    const nyaaStatusCache = new Map(); // 状态: 'loading' | 'found' | 'not-found' | 'error' | 'banned'
    const checkQueue = [];
    let isChecking = false;
    let checkPaused = false;           // 检测过程中再次点「检测」即暂停
    let resumeWaiters = [];            // 暂停期间挂起的唤醒回调
    let banUntil = 0;                  // 冷却截止时间戳
    let progTotal = 0, progDone = 0;   // 本轮检测进度（顶部进度条用）

    const sleep = ms => new Promise(r => setTimeout(r, ms));

    function waitForResume() {
        if (!checkPaused) return Promise.resolve();
        return new Promise(resolve => resumeWaiters.push(resolve));
    }

    function setCheckPaused(paused) {
        if (checkPaused === paused) return;
        checkPaused = paused;
        if (!paused) {
            const waiters = resumeWaiters;
            resumeWaiters = [];
            waiters.forEach(fn => fn());
        }
        updateProgressBar();
        updateToolbar();
        if (paused) toast(`已暂停，剩余 ${checkQueue.length} 个待检测`);
    }

    // 加入检测队列
    function enqueueCheck(num) {
        const status = nyaaStatusCache.get(num);
        // 已出结果或正在检测中，不重复入队
        if (status === 'loading' || status === 'found' || status === 'not-found') {
            updateLinkDom(num);
            return;
        }
        // 冷却期内直接标记为请求频繁，冷却结束后可重试
        if (Date.now() < banUntil) {
            nyaaStatusCache.set(num, 'banned');
            updateLinkDom(num);
            return;
        }
        // 队列已空且不在检测中 —— 视为新一轮，进度清零
        if (!isChecking && checkQueue.length === 0) { progTotal = 0; progDone = 0; }
        nyaaStatusCache.set(num, 'loading');
        if (!checkQueue.includes(num)) { checkQueue.push(num); progTotal++; }
        updateLinkDom(num);
        scheduleProcess();
    }

    /**
     * 延后到微任务再启动队列：调用方通常是一次性批量入队（如「检测」按钮），
     * 若在首个元素入队时就同步起跑，第一批永远只有 1 个，凑不满并发数。
     */
    let queueScheduled = false;
    function scheduleProcess() {
        if (queueScheduled) return;
        queueScheduled = true;
        queueMicrotask(() => {
            queueScheduled = false;
            processQueue();
        });
    }

    /**
     * 批量并发检测：每批 CHECK_CONCURRENCY 个同时发出，
     * 一批全部返回后等待 CHECK_BATCH_WAIT_MS 再发下一批。
     * 暂停时整条循环挂在 waitForResume() 上，已发出的请求仍会正常收尾。
     */
    async function processQueue() {
        if (isChecking) return;
        isChecking = true;
        updateProgressBar();
        updateToolbar();

        try {
            while (checkQueue.length > 0) {
                if (checkPaused) { await waitForResume(); continue; }
                if (Date.now() < banUntil) break;   // 冷却中暂停队列

                const batch = checkQueue.splice(0, CONFIG.CHECK_CONCURRENCY);
                await Promise.all(batch.map(requestStatus));
                updateProgressBar();

                if (checkPaused) continue;          // 暂停时不再消耗批间隔
                if (checkQueue.length) await sleep(CONFIG.CHECK_BATCH_WAIT_MS);
            }
        } finally {
            isChecking = false;
            if (!checkQueue.length) checkPaused = false;   // 没有残留任务时「暂停」无意义
            const waiters = resumeWaiters;
            resumeWaiters = [];
            waiters.forEach(fn => fn());
            updateProgressBar();
            updateToolbar();
        }
    }

    /** 单个番号请求：结果直接写入缓存，Promise 在收尾后 resolve */
    function requestStatus(num) {
        return new Promise(resolve => {
            let settled = false;
            const finish = status => {
                if (settled) return;
                settled = true;
                if (status) nyaaStatusCache.set(num, status);
                progDone++;
                updateLinkDom(num);
                updateProgressBar();
                resolve();
            };

            GM_xmlhttpRequest({
                method: "GET",
                url: nyaaSearchUrl(num),
                anonymous: true,
                timeout: CONFIG.CHECK_TIMEOUT_MS,
                headers: {
                    "User-Agent": navigator.userAgent,
                    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8"
                },
                onload: function(response) {
                    if (response.status === 200) {
                        finish(response.responseText.includes("No results found") ? 'not-found' : 'found');
                    } else if (response.status === 429 || response.status === 403) {
                        banUntil = Date.now() + CONFIG.BAN_COOLDOWN_MS;
                        markQueueBanned();   // 剩余排队项一并标记，避免永久卡在「检测中」
                        finish('banned');
                    } else {
                        finish('error');
                    }
                },
                onerror: function() { finish('error'); },
                ontimeout: function() { finish('error'); }
            });
        });
    }

    /** 被限流时把还在排队的番号一并标为「请求频繁」，并计入进度 */
    function markQueueBanned() {
        if (!checkQueue.length) return;
        checkQueue.forEach(n => {
            nyaaStatusCache.set(n, 'banned');
            progDone++;
            updateLinkDom(n);
        });
        checkQueue.length = 0;
    }

    /** 刷新单行的链接样式与按钮状态（走 rowRefs，不再查 DOM） */
    function updateLinkDom(num) {
        const status = nyaaStatusCache.get(num);

        // 折叠模式下，新判定为无资源的卡片立即折叠（含翻页新载入的）
        if (status === 'not-found' && hideMode) hideCard(num);

        const ref = rowRefs.get(num);
        // 折叠只对当前页生效：前几页的数字格式保持原样，不隐藏
        if (ref && ref.tr) {
            const want = (hideMode && status === 'not-found' && numIndex.has(num)) ? 'none' : '';
            if (ref.tr.style.display !== want) ref.tr.style.display = want;
        }
        if (ref && ref.link) {
            const { link, btn, mark } = ref;
            const cls = STATUS_CLASS[status];
            link.className = cls ? `gm-link ${cls}` : 'gm-link';
            // 状态文案只改一个常驻 span 的 textContent，不解析 HTML、不重建节点
            if (mark) {
                const text = STATUS_TEXT[status] || '';
                if (mark.textContent !== text) mark.textContent = text;
                mark.style.display = text ? '' : 'none';
            }
            if (btn) {
                if (status === 'loading') {
                    btn.disabled = true; btn.textContent = '...'; btn.style.display = '';
                } else if (status === 'error' || status === 'banned') {
                    btn.disabled = false; btn.textContent = '重试'; btn.style.display = '';
                } else if (status) {
                    btn.style.display = 'none';       // found / not-found 已有结论，收起按钮
                } else {
                    btn.disabled = false; btn.textContent = '检测'; btn.style.display = '';
                }
            }
        }
        if (!suppressToolbar) updateToolbar();
        debouncedSaveSession();
    }
    // ===================================

    function debounce(func, wait) {
        let timeoutId = null;
        return function(...args) {
            clearTimeout(timeoutId);
            timeoutId = setTimeout(() => func.apply(this, args), wait);
        };
    }

    function safeOpenTab(url) {
        try { GM_openInTab(url, { active: false, insert: true, setParent: true }); }
        catch (err) { window.open(url, '_blank'); }
    }

    const nyaaSearchUrl = num => `https://sukebei.nyaa.si/?f=0&c=0_0&q=${num}`;
    const supjavSearchUrl = num => `https://supjav.com/zh/?s=${num}`;

    function saveWindowPosition(left, top) {
        if (!left || !top) return; // 未真正移动过则不覆盖已保存的位置
        try { localStorage.setItem(CONFIG.STORAGE_KEY_WIN_POS, JSON.stringify({ left, top })); } catch (e) {}
    }

    function loadWindowPosition() {
        try {
            const posStr = localStorage.getItem(CONFIG.STORAGE_KEY_WIN_POS);
            if (!posStr) return null;
            const pos = JSON.parse(posStr);
            if (!pos || typeof pos.left !== 'string' || typeof pos.top !== 'string') return null;
            if (!pos.left || !pos.top) return null;
            return pos;
        } catch (e) { return null; }
    }

    /** 把悬浮窗夹回可视区域，避免换分辨率后拖不回来 */
    function clampFloatWindow() {
        if (!floatWindow || floatWindow.style.display === 'none') return;
        const rect = floatWindow.getBoundingClientRect();
        if (!rect.width || !rect.height) return;
        let x = parseFloat(floatWindow.style.left);
        let y = parseFloat(floatWindow.style.top);
        if (isNaN(x) || isNaN(y)) return; // 仍为默认 right 定位，不处理
        x = Math.min(Math.max(0, x), Math.max(0, window.innerWidth - rect.width));
        y = Math.min(Math.max(0, y), Math.max(0, window.innerHeight - rect.height));
        floatWindow.style.left = `${x}px`;
        floatWindow.style.top = `${y}px`;
        floatWindow.style.right = 'auto';
    }
    const debouncedClamp = debounce(clampFloatWindow, 200);

    function injectGlobalFonts() {
        if (document.getElementById('gm-global-font-style')) return;
        const fontStyle = document.createElement('style');
        fontStyle.id = 'gm-global-font-style';
        // 排除图标字体承载元素（i / icon、fa- 类名），避免图标变方块
        fontStyle.innerHTML = `
            body, div:not([class*="icon"]):not([class*="fa-"]), p,
            span:not([class*="icon"]):not([class*="fa-"]), a:not([class*="icon"]):not([class*="fa-"]),
            td, th, input, button, textarea, section, article, li, ul, ol, h1, h2, h3, h4, h5, h6 {
                font-family: "Microsoft YaHei", "微软雅黑", -apple-system, BlinkMacSystemFont, sans-serif !important;
            }
            #gm-helper-float-window, #gm-helper-float-window *, #gm-tooltip { font-family: "Microsoft YaHei", "微软雅黑", sans-serif !important; }

            /* 定位：给目标卡片覆盖一层带滤镜的闪烁层，不描边、不影响布局 */
            #gm-locate-overlay {
                position: fixed; pointer-events: none; z-index: ${CONFIG.FLOAT_WIN_ZINDEX - 1};
                display: none; border-radius: 6px;
                background: rgba(255, 152, 0, .22);
                -webkit-backdrop-filter: blur(2px) saturate(1.8);
                backdrop-filter: blur(2px) saturate(1.8);
                box-shadow: inset 0 0 0 2px rgba(255, 152, 0, .9), 0 0 18px rgba(255, 152, 0, .55);
                animation: gm-locate-blink .45s ease-in-out 3 both;
            }
            @keyframes gm-locate-blink {
                0%, 100% { opacity: 0; }
                50% { opacity: 1; }
            }
        `;
        document.head.appendChild(fontStyle);
    }

    // ---------------- 翻译 / 去模糊：统一进帧内批处理队列 ----------------
    const lastTranslated = new WeakMap();  // Text 节点 -> 上次写入的内容，阻断自写自读回环
    let pendingEls = new Set();
    let pendingTexts = new Set();
    let flushHandle = 0;

    const requestFrame = typeof requestAnimationFrame === 'function'
        ? cb => requestAnimationFrame(cb)
        : cb => setTimeout(cb, 16);

    function queueElement(el) {
        pendingEls.add(el);
        scheduleFlush();
    }

    function queueText(node) {
        pendingTexts.add(node);
        scheduleFlush();
    }

    function scheduleFlush() {
        if (flushHandle) return;
        flushHandle = requestFrame(flushQueue);
    }

    /** 每帧统一处理：按文档序剪枝后逐个处理，超预算则顺延到下一帧 */
    function flushQueue() {
        flushHandle = 0;

        if (pendingTexts.size) {
            const texts = pendingTexts;
            pendingTexts = new Set();
            texts.forEach(node => { if (node.isConnected) translateTextNode(node); });
        }

        if (!pendingEls.size) return;
        const els = [];
        pendingEls.forEach(el => { if (el.isConnected) els.push(el); });
        pendingEls = new Set();
        if (!els.length) return;

        // 文档序排序后线性剪枝：被前一个根节点覆盖的直接跳过，避免 O(n²) 两两 contains
        els.sort((a, b) => (a.compareDocumentPosition(b) & Node.DOCUMENT_POSITION_FOLLOWING) ? -1 : 1);
        const roots = [];
        let lastRoot = null;
        for (const el of els) {
            if (lastRoot && lastRoot.contains(el)) continue;
            roots.push(el);
            lastRoot = el;
        }

        let budget = CONFIG.FLUSH_NODE_BUDGET;
        for (let i = 0; i < roots.length; i++) {
            budget -= processElement(roots[i]);
            if (budget <= 0 && i + 1 < roots.length) {
                for (let j = i + 1; j < roots.length; j++) pendingEls.add(roots[j]);
                scheduleFlush();
                return;
            }
        }
    }

    /**
     * 单次遍历同时完成：属性翻译 + 文本翻译 + 去模糊。
     * 返回处理节点数，供帧预算控制（避免长任务卡住滚动）。
     */
    function processElement(rootEl) {
        if (!rootEl || isSkippedEl(rootEl)) return 0;
        let count = 0;
        if (rootEl.nodeType === Node.ELEMENT_NODE) {
            count++;
            translateAttributes(rootEl);
            if (rootEl.tagName === 'IMG') unblurImg(rootEl);
        }

        const walker = document.createTreeWalker(rootEl, NodeFilter.SHOW_ELEMENT | NodeFilter.SHOW_TEXT, {
            acceptNode: n => {
                if (n.nodeType === Node.ELEMENT_NODE) {
                    // REJECT 会连同子树一起剪掉，script / style 内部就此跳过
                    return isSkippedEl(n) ? NodeFilter.FILTER_REJECT : NodeFilter.FILTER_ACCEPT;
                }
                return (n.nodeValue && n.nodeValue.trim() && !isSkippedEl(n.parentElement))
                    ? NodeFilter.FILTER_ACCEPT
                    : NodeFilter.FILTER_REJECT;
            }
        }, false);

        let node;
        while ((node = walker.nextNode())) {
            count++;
            if (node.nodeType === Node.ELEMENT_NODE) {
                translateAttributes(node);
                if (node.tagName === 'IMG') unblurImg(node);
            } else {
                translateTextNode(node);
            }
        }
        return count;
    }

    function translateTextNode(node) {
        const val = node?.nodeValue;
        if (!val || !val.trim()) return;
        if (lastTranslated.get(node) === val) return;   // 上一次是自己写回的，跳过
        if (!TRANS_TEST.test(val)) return;
        const next = translateString(val);
        if (next !== val) {
            node.nodeValue = next;
            lastTranslated.set(node, next);
        }
    }

    function translateAttributes(el) {
        // 遍历元素自身已有的属性（通常 1~3 个），比固定 6 次 getAttribute 便宜
        const attrs = el.attributes;
        for (let i = 0; i < attrs.length; i++) {
            const attr = attrs[i];
            if (!TRANS_ATTRS.has(attr.name)) continue;
            const val = attr.value;
            if (!val || !TRANS_TEST.test(val)) continue;
            const newVal = translateString(val);
            if (newVal !== val) el.setAttribute(attr.name, newVal);
        }
    }

    function unblurImg(imgEl) {
        if (!imgEl || imgEl.tagName !== 'IMG') return;
        const blurClasses = Array.from(imgEl.classList).filter(c => c.includes('blur'));
        const inlineBlur = /blur\(/i.test(imgEl.style.filter || '') || /blur\(/i.test(imgEl.style.backdropFilter || '');
        // 已无模糊则直接返回：省性能，也避免与 observer 形成回环
        if (!blurClasses.length && !inlineBlur) return;

        blurClasses.forEach(cls => imgEl.classList.remove(cls));
        imgEl.classList.add('gm-img-clear');
        // 必须用 setProperty 才能带 !important；直接赋值 'none !important' 会被浏览器整条丢弃
        imgEl.style.setProperty('filter', 'none', 'important');
        imgEl.style.setProperty('backdrop-filter', 'none', 'important');
    }

    function batchUnblurAllImg() {
        document.querySelectorAll('img[class*="blur"], img[style*="blur"]').forEach(unblurImg);
    }

    // ---------------- 番号提取 + 元素索引 ----------------
    /** 由番号节点反推它所在的卡片容器（用于定位与折叠） */
    function resolveCard(badge) {
        let node = badge.parentElement;
        let depth = 0;
        while (node && node !== document.body && depth < 6) {
            if (node.matches(CARD_SELECTOR) && node.querySelectorAll(ID_BADGE_SELECTOR).length === 1) return node;
            node = node.parentElement;
            depth++;
        }
        return badge.parentElement || badge;
    }

    /** 从元素文本中提取 6~7 位番号，规避 8 位以上数字串的误匹配 */
    function collectIds(root, index) {
        if (!root || (floatWindow && floatWindow.contains(root))) return;
        const txt = root.textContent;
        if (!txt) return;
        for (const m of txt.matchAll(NUMBER_SCAN_RE)) {
            const start = m.index;
            const prevChar = txt[start - 1];
            const nextChar = txt[start + m[0].length];
            if ((prevChar && /\d/.test(prevChar)) || (nextChar && /\d/.test(nextChar))) continue;
            const num = m[0];
            if (!index.has(num)) index.set(num, { el: root, card: resolveCard(root) });
        }
    }

    function scanNumbers() {
        const index = new Map();
        let nodes = document.querySelectorAll(ID_BADGE_SELECTOR);
        if (!nodes.length) nodes = document.querySelectorAll(FALLBACK_ID_SELECTORS.join(','));
        nodes.forEach(el => collectIds(el, index));
        return index;
    }

    function extractSevenDigitNumbers() {
        syncScope();               // 换列表（路径/搜索条件变了）先把旧数字清干净
        const index = scanNumbers();
        const pageNo = currentPageNo();

        // 刚换过列表：以本次扫描为权威，直接覆盖（防止「先改地址、后换内容」时把旧页数字又捞回来）
        const rebuild = Date.now() < scopeSettleUntil;
        let isChanged = false;

        if (rebuild) {
            isChanged = index.size !== foundNumbers.size;
            foundNumbers = new Set(index.keys());
            numPage.clear();
            index.forEach((entry, num) => numPage.set(num, pageNo));
        } else {
            // 同一列表内（翻页）：只做累加，前几页留下的数字不受影响
            index.forEach((entry, num) => {
                numPage.set(num, pageNo);
                if (!foundNumbers.has(num)) { foundNumbers.add(num); isChanged = true; }
            });
        }

        numIndex = index;          // 元素引用每次刷新（页面可能重渲染），只代表当前页
        updateToolbar();

        // 站点重渲染后，已折叠的卡片会被换掉，这里按缓存状态补折叠（已是隐藏态则跳过）
        if (hideMode) {
            nyaaStatusCache.forEach((status, num) => { if (status === 'not-found') hideCard(num); });
        }

        if (isChanged) updateFloatWindow();
        else updateRowPageState();   // 数字没变但本页映射可能变了，刷新定位可用性

        debouncedSaveSession();
    }
    const debouncedExtractNum = debounce(extractSevenDigitNumbers, CONFIG.DEBOUNCE_WAIT);

    /**
     * 把列表「重置为当前页」：清空其他页留下的番号、所属页码与检测结论。
     * 只保留当前页扫到的数字（本页已有的检测结果不动）。
     * @returns {number} 被清掉的其他页番号个数
     */
    function resetToCurrentPage(index) {
        const keep = new Set(index.keys());
        let removed = 0;

        Array.from(foundNumbers).forEach(num => {
            if (keep.has(num)) return;
            foundNumbers.delete(num);
            numPage.delete(num);
            nyaaStatusCache.delete(num);
            removed++;
        });

        // 其他页还没检测完的排队项一并丢掉，避免列表已清空、后台却还在发请求
        for (let i = checkQueue.length - 1; i >= 0; i--) {
            if (!keep.has(checkQueue[i])) {
                checkQueue.splice(i, 1);
                progTotal = Math.max(progDone, progTotal - 1);
            }
        }
        return removed;
    }

    /**
     * 彻底清空列表状态（换列表时用）：数字、页码、检测结论、排队请求、表格。
     * 与本页折叠的卡片先还原，避免把旧页卡片藏在新页里。
     */
    function clearListState() {
        hiddenCards.forEach((prev, el) => { if (el.isConnected) el.style.display = prev; });
        hiddenCards.clear();
        foundNumbers.clear();
        numPage.clear();
        nyaaStatusCache.clear();
        rowRefs.clear();
        numIndex = new Map();
        checkQueue.length = 0;
        progTotal = 0;
        progDone = 0;
        renderedSig = null;              // 下次 updateFloatWindow 强制重绘成空表
        updateFloatWindow(true);
        updateProgressBar();
    }

    /**
     * 列表身份变了就清空。身份 = pathname + 除 page 以外的查询参数：
     *   /news?page=1 → /news?page=2   同一列表，保留数字
     *   /news?page=1 → /              路径变了，清空
     *   /news?page=1 → /wiki?page=1   路径变了，清空
     *   ?q=a → ?q=b                   搜索条件变了，清空
     * @returns {boolean} 是否发生了清空
     */
    function syncScope() {
        let scope;
        try { scope = listScope(); } catch (e) { return false; }
        if (scope === activeScope) return false;
        activeScope = scope;
        scopeSettleUntil = Date.now() + CONFIG.SCOPE_SETTLE_MS;
        clearListState();
        return true;
    }

    /** 监听地址变化：站内可能用 pushState 跳转（不整页刷新），此时必须自己清空 */
    function watchUrlChanges() {
        const onChange = () => {
            const had = foundNumbers.size;
            if (syncScope()) {
                if (had) toast(`列表已切换，旧列表的 ${had} 个数字已清空`);
                debouncedExtractNum();
            }
        };

        ['pushState', 'replaceState'].forEach(fn => {
            const orig = history[fn];
            if (typeof orig !== 'function') return;
            history[fn] = function (...args) {
                const ret = orig.apply(this, args);
                try { onChange(); } catch (e) {}
                return ret;
            };
        });
        window.addEventListener('popstate', onChange);
        window.addEventListener('hashchange', onChange);

        // 兜底：个别站点直接改 location 或用框架接管路由，轮询一次代价极低
        setInterval(() => { if (listScope() !== activeScope) onChange(); }, 1000);
    }

    /** 每行「是否在当前页」变化后，同步定位按钮的可用性（隐藏逻辑也依赖它） */    function updateRowPageState() {
        rowRefs.forEach((ref, num) => {
            const onPage = numIndex.has(num);
            if (ref.off === !onPage) return;
            ref.off = !onPage;
            if (ref.loc) {
                ref.loc.disabled = !onPage;
                ref.loc.title = onPage
                    ? `定位到页面中的 ${num}`
                    : `该番号在第 ${numPage.get(num) || '?'} 页，当前页无法定位`;
            }
        });
    }

    // ---------------- 交互反馈：悬停详情 ----------------
    let tipEl = null;
    let tipTimer = 0;

    function ensureTip() {
        if (tipEl && tipEl.isConnected) return tipEl;
        tipEl = document.createElement('div');
        tipEl.id = 'gm-tooltip';
        tipEl.style.display = 'none';
        document.body.appendChild(tipEl);
        return tipEl;
    }

    function showTip(anchor, text) {
        const el = ensureTip();
        el.textContent = text;
        el.style.display = 'block';
        const r = anchor.getBoundingClientRect();
        const tr = el.getBoundingClientRect();
        let left = Math.min(Math.max(6, r.left + r.width / 2 - tr.width / 2), Math.max(6, window.innerWidth - tr.width - 6));
        let top = r.top - tr.height - 8;
        if (top < 6) top = r.bottom + 8;
        el.style.left = `${left}px`;
        el.style.top = `${top}px`;
    }

    function hideTip() {
        clearTimeout(tipTimer);
        if (tipEl) tipEl.style.display = 'none';
    }

    function attachTip(el, textFn) {
        if (!el) return;
        el.addEventListener('mouseenter', () => {
            clearTimeout(tipTimer);
            tipTimer = setTimeout(() => { if (el.isConnected) showTip(el, textFn()); }, CONFIG.TIP_DELAY_MS);
        });
        el.addEventListener('mouseleave', hideTip);
        el.addEventListener('click', hideTip);
    }

    /** 短暂提示（用于「已刷新」「链接超上限」这类一次性反馈） */
    function toast(msg) {
        if (!floatWindow) return;
        const anchor = floatWindow.querySelector('#gm-count-display') || floatWindow;
        showTip(anchor, msg);
        clearTimeout(tipTimer);
        tipTimer = setTimeout(hideTip, 1600);
    }

    // ---------------- 统计 ----------------
    function statusCounts() {
        let found = 0, none = 0, bad = 0, pending = 0;
        foundNumbers.forEach(n => {
            const s = nyaaStatusCache.get(n);
            if (s === 'found') found++;
            else if (s === 'not-found') none++;
            else if (s === 'error' || s === 'banned') bad++;
            else if (!s) pending++;
        });
        return { total: foundNumbers.size, found, none, bad, pending };
    }

    function countTip() {
        const c = statusCounts();
        const lines = [
            `共 ${c.total} 个番号`,
            `有资源 ${c.found} · 无资源 ${c.none}`,
            `待检测 ${c.pending}${c.bad ? ` · 失败 ${c.bad}` : ''}`
        ];
        const off = c.total - numIndex.size;
        if (off > 0) lines.push(`当前页 ${numIndex.size} 个 · 前几页 ${off} 个（不可定位/隐藏）`);
        if (hideMode) lines.push(`已折叠 ${hiddenCards.size} 个无资源卡片`);
        return lines.join('\n');
    }

    function checkTip() {
        const c = statusCounts();
        if (checkPaused) return `已暂停，再次点击继续检测\n剩余 ${checkQueue.length} 个待检测`;
        if (isChecking) return `检测中（每批 5 个并发，批间隔 1 秒）\n再次点击可暂停\n剩余 ${checkQueue.length} 个待检测`;
        return `只检测尚未检测过的新番号\n当前待检测 ${c.pending} 个（已完成的不重复检测）\n每批 5 个并发，一批结束后等 1 秒继续`;
    }

    function openTip() {
        const c = statusCounts();
        if (!c.found) return '暂不可用：需先检测出至少一个有资源的番号';
        const n = Math.min(c.found, CONFIG.OPEN_ALL_MAX);
        return `一键打开 ${n} 个有资源的下载页${c.found > n ? `（上限 ${CONFIG.OPEN_ALL_MAX}）` : ''}`;
    }

    function hideTipText() {
        if (hideMode) return `恢复显示已折叠的 ${hiddenCards.size} 个无资源卡片`;
        return `折叠当前页所有无资源番号的卡片\n页面自动重排，悬浮窗内本页对应行一起隐藏\n（前几页的数字不受影响）`;
    }

    // ---------------- 折叠 / 定位 / 一键打开 ----------------
    function hideCard(num) {
        const entry = numIndex.get(num);
        const card = entry?.card;
        if (!card || !card.isConnected || hiddenCards.has(card)) return;
        hiddenCards.set(card, card.style.display || '');
        card.style.display = 'none';
    }

    function applyHideState() {
        // 先恢复全部，再按当前判定重新折叠，保证「恢复」不留残留
        hiddenCards.forEach((prev, el) => { if (el.isConnected) el.style.display = prev; });
        hiddenCards.clear();
        if (hideMode) {
            nyaaStatusCache.forEach((status, num) => { if (status === 'not-found') hideCard(num); });
        }
        // 悬浮窗内同步：折叠时无资源行一起隐藏，恢复时全部放回
        suppressToolbar = true;
        foundNumbers.forEach(n => updateLinkDom(n));
        suppressToolbar = false;
        updateToolbar();
    }

    function toggleHide() {
        hideMode = !hideMode;
        applyHideState();
        updateToolbar();
        toast(hideMode ? `已折叠 ${hiddenCards.size} 个无资源卡片（列表同步隐藏）` : '已恢复显示');
    }

    let locateOverlay = null;
    let locateRaf = 0;

    function clearLocateFlash() {
        if (locateRaf) { cancelAnimationFrame(locateRaf); locateRaf = 0; }
        if (locateOverlay && locateOverlay.isConnected) locateOverlay.remove();
        locateOverlay = null;
    }

    /**
     * 在目标卡片上方覆盖一层「滤镜」并闪烁几下。
     * 用 fixed 定位的独立覆盖层逐帧跟随卡片矩形，不改动页面元素自身的
     * position / class，因此不会引起重排，也不会被站点的样式覆盖掉。
     */
    function flashCard(card) {
        clearLocateFlash();
        const overlay = document.createElement('div');
        overlay.id = 'gm-locate-overlay';
        document.body.appendChild(overlay);
        locateOverlay = overlay;

        const start = performance.now();
        const tick = () => {
            locateRaf = 0;
            if (!overlay.isConnected) return;
            if (!card || !card.isConnected) { clearLocateFlash(); return; }

            const r = card.getBoundingClientRect();
            if (r.width && r.height) {
                overlay.style.display = 'block';
                overlay.style.left = `${r.left}px`;
                overlay.style.top = `${r.top}px`;
                overlay.style.width = `${r.width}px`;
                overlay.style.height = `${r.height}px`;
            }
            if (performance.now() - start >= CONFIG.LOCATE_FLASH_MS) { clearLocateFlash(); return; }
            locateRaf = requestAnimationFrame(tick);
        };
        locateRaf = requestAnimationFrame(tick);
    }

    function locateNum(num) {
        const entry = numIndex.get(num);
        const card = entry?.card;
        const target = (card && card.isConnected) ? card : entry?.el;
        if (!target || !target.isConnected) { toast('页面中未找到该番号，可能已随翻页卸载'); return; }

        // 折叠状态下定位：先把目标卡片放出来
        if (card && hiddenCards.has(card)) {
            card.style.display = hiddenCards.get(card) || '';
            hiddenCards.delete(card);
        }
        target.scrollIntoView({ behavior: 'smooth', block: 'center' });
        flashCard(target);
    }

    function openAllFound() {
        const nums = [];
        foundNumbers.forEach(n => { if (nyaaStatusCache.get(n) === 'found') nums.push(n); });
        if (!nums.length) { toast('暂无可打开的链接，请先检测'); return; }
        const list = nums.sort((a, b) => a - b).slice(0, CONFIG.OPEN_ALL_MAX);
        list.forEach((n, i) => setTimeout(() => safeOpenTab(nyaaSearchUrl(n)), i * 120));
        toast(`正在打开 ${list.length} 个链接${nums.length > list.length ? '（已达上限）' : ''}`);
    }

    /** 只检测「从未检测过」的新番号，已出结果/已失败的不重复请求 */
    function checkNewOnly() {
        const pending = [];
        foundNumbers.forEach(n => { if (!nyaaStatusCache.has(n)) pending.push(n); });
        pending.sort((a, b) => a - b).forEach(enqueueCheck);
        return pending.length;
    }

    // ---------------- 跨页会话：翻页后保留已收集的番号与检测结果 ----------------
    /**
     * 站点翻页是整页刷新的 ?page=N。这里用 sessionStorage 把番号与检测状态带到下一页：
     * 只有「pathname + 除 page 外的查询参数」完全一致（scope 相同）才继承，
     * 换了搜索词/筛选条件就是另一个列表，从头开始。
     */
    const SESSION_KEY = 'fc2cmadb_session';

    function currentPageNo() {
        try {
            const p = parseInt(new URL(location.href).searchParams.get('page') || '1', 10);
            return (Number.isNaN(p) || p < 1) ? 1 : p;
        } catch (e) { return 1; }
    }

    /** 列表身份：pathname + 除 page 外的全部查询参数（与顺序无关） */
    function listScope() {
        try {
            const u = new URL(location.href);
            const pairs = [];
            u.searchParams.forEach((v, k) => { if (k !== 'page') pairs.push(`${k}=${v}`); });
            pairs.sort();
            return `${u.pathname}?${pairs.join('&')}`;
        } catch (e) { return 'unknown'; }
    }

    const SESSION_SCOPE = listScope();
    activeScope = SESSION_SCOPE;          // 当前列表身份，地址变化时同步
    let restoredCount = 0;                // 从上一页继承来的番号数量

    /**
     * 把会话里属于本列表的条目并回内存。
     * 只做「补」，不删除任何已有数字，所以可以安全地在刷新时重复调用。
     */
    function mergeSessionEntries() {
        let data = null;
        try {
            const raw = sessionStorage.getItem(SESSION_KEY);
            if (!raw) return 0;
            data = JSON.parse(raw);
        } catch (e) { return 0; }
        if (!data || data.scope !== activeScope || !Array.isArray(data.entries)) return 0;

        let added = 0;
        data.entries.forEach(item => {
            if (!Array.isArray(item)) return;
            const [num, status, page] = item;
            if (typeof num !== 'string' || !num) return;
            if (!foundNumbers.has(num)) added++;
            foundNumbers.add(num);
            if (!numPage.has(num)) numPage.set(num, page || 1);
            // 内存里已有结论的不覆盖；loading / banned 只是临时态，跨页后当作未检测
            if (!nyaaStatusCache.has(num) && status && status !== 'loading' && status !== 'banned') {
                nyaaStatusCache.set(num, status);
            }
        });
        return added;
    }

    function restoreSession() {
        restoredCount = mergeSessionEntries();
    }

    function saveSession() {
        try {
            const page = currentPageNo();
            const entries = [];
            for (const num of foundNumbers) {
                if (entries.length >= CONFIG.SESSION_MAX) break;
                entries.push([num, nyaaStatusCache.get(num) || '', numPage.get(num) || page]);
            }
            sessionStorage.setItem(SESSION_KEY, JSON.stringify({ scope: activeScope, page, entries }));
        } catch (e) {}
    }
    const debouncedSaveSession = debounce(saveSession, CONFIG.SAVE_DEBOUNCE_MS);

    // ---------------- 悬浮窗 ----------------
    function createFloatWindowStyle() {
        if (document.getElementById('gm-float-win-style')) return;
        const style = document.createElement('style');
        style.id = 'gm-float-win-style';
        style.innerHTML = `
            #gm-helper-float-window {
                position: fixed; right: 20px; top: 100px;
                z-index: ${CONFIG.FLOAT_WIN_ZINDEX}; min-width: ${CONFIG.FLOAT_WIN_WIDTH}px;
                background: var(--gm-bg); color: var(--gm-fg);
                border: 1px solid var(--gm-border);
                box-shadow: 0 4px 14px rgba(0,0,0,0.18); border-radius: 8px;
                font-size: 13px; overflow: hidden;
                --gm-bg: #fff; --gm-fg: #333; --gm-border: #ccc; --gm-head: #f5f5f5;
                --gm-btn-bg: #fff; --gm-btn-border: #ccc; --gm-btn-fg: #333; --gm-btn-hover: #e9e9e9;
                --gm-cell: #eee; --gm-link: #0066cc; --gm-link-hover: #004499; --gm-muted: #999;
                --gm-danger: #e74c3c; --gm-warn: #f39c12; --gm-ban: #8e44ad; --gm-ok: #2ecc71;
            }
            #gm-helper-float-window.gm-dark {
                --gm-bg: #1f2124; --gm-fg: #e8e8e8; --gm-border: #3a3d42; --gm-head: #2a2d31;
                --gm-btn-bg: #2a2d31; --gm-btn-border: #45494f; --gm-btn-fg: #e8e8e8; --gm-btn-hover: #3a3e44;
                --gm-cell: #34383d; --gm-link: #6cb6ff; --gm-link-hover: #9ccfff; --gm-muted: #8b9096;
            }
            #gm-helper-header {
                display: flex; align-items: center; gap: 6px; padding: 6px 8px;
                background: var(--gm-head); border-bottom: 1px solid var(--gm-border); user-select: none;
            }
            #gm-helper-toolbar {
                display: flex; gap: 6px; padding: 6px 8px;
                background: var(--gm-bg); border-bottom: 1px solid var(--gm-border);
            }
            .gm-spacer { flex: 1; }
            .gm-icon-btn {
                width: 24px; height: 24px; padding: 0; flex: none;
                display: inline-flex; align-items: center; justify-content: center;
                border: 1px solid var(--gm-btn-border); background: var(--gm-btn-bg);
                color: var(--gm-btn-fg); border-radius: 4px; cursor: pointer; font-size: 13px; line-height: 1;
            }
            .gm-icon-btn:hover { background: var(--gm-btn-hover); }
            #gm-drag { cursor: move; }
            #gm-helper-close { color: var(--gm-danger); font-weight: bold; font-size: 15px; }
            .gm-count-btn {
                min-width: 34px; padding: 2px 8px; flex: none;
                border: 1px solid var(--gm-btn-border); background: var(--gm-btn-bg);
                color: var(--gm-link); font-weight: 700; font-size: 13px;
                border-radius: 10px; cursor: pointer;
            }
            .gm-count-btn:hover { background: var(--gm-btn-hover); }
            .gm-btn {
                flex: 1; padding: 4px 6px; cursor: pointer; font-size: 12px;
                border: 1px solid var(--gm-btn-border); background: var(--gm-btn-bg);
                color: var(--gm-btn-fg); border-radius: 4px;
            }
            .gm-btn:hover:not(.gm-disabled) { background: var(--gm-btn-hover); }
            .gm-btn.gm-disabled { opacity: .45; cursor: not-allowed; }
            .gm-btn.gm-running { border-color: var(--gm-warn); color: var(--gm-warn); font-weight: 700; }
            .gm-btn.gm-paused { border-color: var(--gm-ban); color: var(--gm-ban); font-weight: 700; }

            /* 检测进度：紧贴数量按钮右侧，与标题栏同一行，不额外占高度 */
            #gm-progress {
                display: none; align-items: center; gap: 5px;
                flex: 0 1 auto; min-width: 0; padding: 0;
                font-size: 10px; color: var(--gm-muted); line-height: 1;
            }
            #gm-progress-track {
                flex: 0 1 56px; width: 56px; height: 4px; border-radius: 2px;
                background: var(--gm-cell); overflow: hidden;
            }
            #gm-progress-bar {
                width: 0; height: 100%; border-radius: 2px;
                background: var(--gm-link); transition: width .2s linear;
            }
            #gm-progress.gm-paused #gm-progress-bar { background: var(--gm-warn); }
            #gm-progress-text {
                flex: 0 1 auto; min-width: 0; white-space: nowrap;
                overflow: hidden; text-overflow: ellipsis;
                font-variant-numeric: tabular-nums;
            }

            #gm-helper-body { max-height: ${CONFIG.FLOAT_WIN_MAX_HEIGHT}px; overflow-y: auto; padding: 6px 8px 8px; }
            #gm-helper-body::-webkit-scrollbar { width: 6px; }
            #gm-helper-body::-webkit-scrollbar-thumb { background: var(--gm-muted); border-radius: 3px; }

            .gm-table { width: 100%; border-collapse: collapse; text-align: center; }
            .gm-table th, .gm-table td { border: 1px solid var(--gm-cell); padding: 4px 5px; vertical-align: middle; }
            .gm-table th { color: var(--gm-muted); font-weight: normal; font-size: 11px; }
            .gm-col-loc { width: 34px; padding: 0 !important; }
            /* 定位：整格一个大按钮，而不是一个裸符号 */
            .gm-locate {
                display: block; width: 100%; min-height: 26px; padding: 0;
                border: 1px solid var(--gm-btn-border); border-radius: 4px;
                background: var(--gm-btn-bg); color: var(--gm-link);
                cursor: pointer; font-size: 14px; line-height: 1;
            }
            .gm-locate:hover:not(:disabled) { background: var(--gm-link); border-color: var(--gm-link); color: #fff; }
            .gm-locate:active:not(:disabled) { transform: scale(.97); }
            /* 前几页带过来的番号不在当前 DOM 里，无法定位 */
            .gm-locate:disabled {
                opacity: .3; cursor: not-allowed;
                border-color: var(--gm-cell); background: transparent; color: var(--gm-muted);
            }
            .gm-link { color: var(--gm-link); text-decoration: none; cursor: pointer; font-weight: bold; }
            .gm-link:hover { text-decoration: underline; color: var(--gm-link-hover); }
            .gm-status { font-size: 11px; margin-left: 4px; }
            .gm-link.not-found { color: var(--gm-danger) !important; text-decoration: line-through; }
            .gm-link.loading { color: var(--gm-muted) !important; font-weight: normal; }
            .gm-link.error { color: var(--gm-warn) !important; }
            .gm-link.banned { color: var(--gm-ban) !important; }
            .gm-check-btn {
                margin-left: 6px; padding: 1px 5px; font-size: 11px; cursor: pointer;
                border: 1px solid var(--gm-link); background: var(--gm-btn-bg);
                color: var(--gm-link); border-radius: 4px;
            }
            .gm-check-btn:hover:not(:disabled) { background: var(--gm-link); color: #fff; }
            .gm-check-btn:disabled { border-color: var(--gm-border); color: var(--gm-muted); background: var(--gm-btn-hover); cursor: not-allowed; }

            #gm-tooltip {
                position: fixed; z-index: ${CONFIG.FLOAT_WIN_ZINDEX + 1};
                max-width: 260px; padding: 7px 10px;
                background: rgba(18,18,18,.94); color: #fff; font-size: 12px; line-height: 1.55;
                border-radius: 6px; pointer-events: none; white-space: pre-line;
                box-shadow: 0 4px 14px rgba(0,0,0,.35); display: none;
            }
        `;
        document.head.appendChild(style);
    }

    function createFloatWindow() {
        if (document.getElementById('gm-helper-float-window')) return;
        createFloatWindowStyle();

        floatWindow = document.createElement('div');
        floatWindow.id = 'gm-helper-float-window';
        floatWindow.innerHTML = `
            <div id="gm-helper-header">
                <button id="gm-drag" class="gm-icon-btn" aria-label="拖动">⠿</button>
                <button id="gm-count-display" class="gm-count-btn">0</button>
                <div id="gm-progress" style="display:none;">
                    <span id="gm-progress-text">检测 0/0</span>
                    <div id="gm-progress-track"><div id="gm-progress-bar"></div></div>
                </div>
                <span class="gm-spacer"></span>
                <button id="gm-theme-toggle" class="gm-icon-btn" aria-label="切换主题">🌙</button>
                <button id="gm-helper-close" class="gm-icon-btn" aria-label="关闭">×</button>
            </div>
            <div id="gm-helper-toolbar">
                <button id="gm-btn-check" class="gm-btn">检测</button>
                <button id="gm-btn-open" class="gm-btn gm-disabled" aria-disabled="true">打开</button>
                <button id="gm-btn-hide" class="gm-btn">隐藏</button>
                <button id="gm-btn-refresh" class="gm-btn">刷新</button>
            </div>
            <div id="gm-helper-body">
                <table class="gm-table">
                    <thead><tr><th class="gm-col-loc"></th><th>下载链接</th><th>在线播放</th></tr></thead>
                    <tbody id="gm-table-body"></tbody>
                </table>
            </div>
        `;
        document.body.appendChild(floatWindow);

        const $ = sel => floatWindow.querySelector(sel);
        const countBtn = $('#gm-count-display');
        const checkBtn = $('#gm-btn-check');
        const openBtn = $('#gm-btn-open');
        const hideBtn = $('#gm-btn-hide');
        const refreshBtn = $('#gm-btn-refresh');
        const themeBtn = $('#gm-theme-toggle');

        // 恢复上次的坐标与主题
        const lastPos = loadWindowPosition();
        if (lastPos) {
            floatWindow.style.left = lastPos.left;
            floatWindow.style.top = lastPos.top;
            floatWindow.style.right = 'auto';
            clampFloatWindow();
        }
        applyTheme(currentTheme());
        window.addEventListener('resize', debouncedClamp);

        // 只有拖动柄能拖动整个窗口
        $('#gm-drag').addEventListener('mousedown', dragStart);

        // 事件委托：定位 / 链接 / 单行检测
        floatWindow.addEventListener('click', e => {
            const locate = e.target.closest('.gm-locate');
            if (locate) {
                e.preventDefault();
                locateNum(locate.getAttribute('data-locate'));
                return;
            }
            const link = e.target.closest('.gm-link');
            if (link) {
                e.preventDefault();
                safeOpenTab(link.getAttribute('href'));
                setTimeout(() => window.focus(), 50);
                return;
            }
            const checkOne = e.target.closest('.gm-check-btn');
            if (checkOne && !checkOne.disabled) {
                const num = checkOne.getAttribute('data-check');
                if (num) enqueueCheck(num);
            }
        });

        $('#gm-helper-close').addEventListener('click', () => {
            userClosed = true;
            hideTip();
            floatWindow.style.display = 'none';
        });

        themeBtn.addEventListener('click', toggleTheme);
        countBtn.addEventListener('click', () => { showTip(countBtn, countTip()); clearTimeout(tipTimer); tipTimer = setTimeout(hideTip, 2400); });

        checkBtn.addEventListener('click', () => {
            // 检测中点击 = 暂停；暂停中点击 = 继续；空闲点击 = 只检测尚未检测过的新番号
            if (checkPaused) { setCheckPaused(false); return; }
            if (isChecking) { setCheckPaused(true); return; }

            const n = checkNewOnly();
            if (!n) { toast('没有待检测的新番号'); return; }
            updateProgressBar();
        });

        openBtn.addEventListener('click', () => {
            if (openBtn.getAttribute('aria-disabled') === 'true') { toast('暂无可打开的链接，请先检测'); return; }
            openAllFound();
        });

        hideBtn.addEventListener('click', () => {
            if (!hideMode && statusCounts().none === 0) { toast('当前没有判定为无资源的番号'); return; }
            toggleHide();
        });

        refreshBtn.addEventListener('click', () => {
            userClosed = false;
            // 刷新 = 以当前页为准重建列表：清空其他页的数字与检测结果，
            // 本页的数字保留（已有的检测结论也保留），并补一遍翻译/去模糊。
            const index = scanNumbers();
            if (!index.size) { toast('当前页没扫到番号，已跳过（未清空列表）'); return; }

            const removed = resetToCurrentPage(index);
            batchUnblurAllImg();
            queueElement(document.body);
            extractSevenDigitNumbers();          // 把本页数字并入并重绘表格
            if (hideMode) applyHideState();      // 折叠状态继续生效（只作用于本页）
            floatWindow.style.display = 'block';
            updateFloatWindow(true);
            saveSession();                       // 立即落盘，避免刷新后又从会话里把前几页捞回来
            toast(removed
                ? `已刷新：清掉其他页 ${removed} 个，仅保留本页 ${numIndex.size} 个`
                : `已刷新：仅保留本页 ${numIndex.size} 个`);
        });

        // 悬停详情
        attachTip(countBtn, countTip);
        attachTip(checkBtn, checkTip);
        attachTip(openBtn, openTip);
        attachTip(hideBtn, hideTipText);
        attachTip(refreshBtn, () => '以当前页为准重建列表\n清空其他页的数字与检测结果，只保留本页的数字（本页结论保留）\n同时补翻译、去模糊，并清除已失效的定位');
        attachTip(themeBtn, () => `切换到${floatWindow.classList.contains('gm-dark') ? '白天' : '黑暗'}模式`);
        attachTip($('#gm-drag'), () => '按住拖动悬浮窗');
        attachTip($('#gm-progress'), progressTip);
    }

    function dragStart(e) {
        if (e.button !== 0) return;
        e.preventDefault();
        e.stopPropagation();
        hideTip();
        const rect = floatWindow.getBoundingClientRect();
        const shiftX = e.clientX - rect.left, shiftY = e.clientY - rect.top;
        let moved = false;

        function moveHandler(evt) {
            let x = evt.clientX - shiftX, y = evt.clientY - shiftY;
            const winW = window.innerWidth, winH = window.innerHeight;
            const boxW = floatWindow.offsetWidth, boxH = floatWindow.offsetHeight;
            if (x < 0) x = 0; if (y < 0) y = 0;
            if (x + boxW > winW) x = winW - boxW; if (y + boxH > winH) y = winH - boxH;
            floatWindow.style.left = `${x}px`; floatWindow.style.top = `${y}px`; floatWindow.style.right = 'auto';
            winDragPos.left = `${x}px`; winDragPos.top = `${y}px`;
            moved = true;
        }
        function upHandler() {
            document.removeEventListener('mousemove', moveHandler);
            document.removeEventListener('mouseup', upHandler);
            // 只有真正拖动过才写入位置，避免「点一下」把已保存坐标清空
            if (moved) saveWindowPosition(winDragPos.left, winDragPos.top);
        }
        document.addEventListener('mousemove', moveHandler);
        document.addEventListener('mouseup', upHandler, { once: true });
    }

    // ---------------- 主题 ----------------
    function currentTheme() {
        try { return localStorage.getItem(CONFIG.STORAGE_KEY_THEME) === 'dark' ? 'dark' : 'light'; }
        catch (e) { return 'light'; }
    }

    function applyTheme(theme) {
        if (!floatWindow) return;
        const dark = theme === 'dark';
        floatWindow.classList.toggle('gm-dark', dark);
        const btn = floatWindow.querySelector('#gm-theme-toggle');
        if (btn) btn.textContent = dark ? '☀' : '🌙';
        try { localStorage.setItem(CONFIG.STORAGE_KEY_THEME, theme); } catch (e) {}
    }

    function toggleTheme() {
        applyTheme(floatWindow.classList.contains('gm-dark') ? 'light' : 'dark');
        hideTip();
    }

    // ---------------- 表格渲染 ----------------
    function rowHtml(num) {
        const onPage = numIndex.has(num);
        const locTitle = onPage
            ? `定位到页面中的 ${num}`
            : `该番号在第 ${numPage.get(num) || '?'} 页，当前页无法定位`;
        return `<tr data-num="${num}">` +
            `<td class="gm-col-loc"><button class="gm-locate" data-locate="${num}"${onPage ? '' : ' disabled'} title="${locTitle}">◎</button></td>` +
            `<td><a href="${nyaaSearchUrl(num)}" class="gm-link" data-nyaa="${num}">${num}` +
            `<span class="gm-status" style="display:none;"></span></a>` +
            `<button class="gm-check-btn" data-check="${num}" style="display:none;">检测</button></td>` +
            `<td><a href="${supjavSearchUrl(num)}" class="gm-link">${num}</a></td></tr>`;
    }

    function updateFloatWindow(force = false) {
        if (!floatWindow) createFloatWindow();
        if (!userClosed || force) floatWindow.style.display = 'block';

        const tbody = document.getElementById('gm-table-body');
        const bodyWrap = document.getElementById('gm-helper-body');
        const prevScrollTop = bodyWrap ? bodyWrap.scrollTop : 0;

        const numArr = Array.from(foundNumbers).sort((a, b) => a - b);
        const sig = numArr.join(',');

        if (sig !== renderedSig) {
            renderedSig = sig;
            rowRefs.clear();
            // 一次性写入，避免 N 次 createElement + 逐行重排
            tbody.innerHTML = numArr.map(rowHtml).join('');
            const trs = tbody.children;
            for (let i = 0; i < numArr.length; i++) {
                rowRefs.set(numArr[i], {
                    tr: trs[i],
                    loc: trs[i].querySelector('.gm-locate'),
                    link: trs[i].querySelector('a[data-nyaa]'),
                    mark: trs[i].querySelector('.gm-status'),
                    btn: trs[i].querySelector('button[data-check]'),
                    off: !numIndex.has(numArr[i])
                });
            }
            suppressToolbar = true;
            numArr.forEach(updateLinkDom);   // 回填缓存状态（含重绘后的按钮态）
            suppressToolbar = false;
            pruneStatusCache();
        }

        updateToolbar();
        if (bodyWrap) bodyWrap.scrollTop = prevScrollTop;
    }

    function updateToolbar() {
        if (!floatWindow) return;
        const c = statusCounts();
        const countBtn = floatWindow.querySelector('#gm-count-display');
        if (countBtn) countBtn.textContent = String(c.total);

        const checkBtn = floatWindow.querySelector('#gm-btn-check');
        if (checkBtn) {
            const label = checkPaused ? '继续' : (isChecking ? '暂停' : '检测');
            if (checkBtn.textContent !== label) checkBtn.textContent = label;
            checkBtn.classList.toggle('gm-running', isChecking && !checkPaused);
            checkBtn.classList.toggle('gm-paused', checkPaused);
        }

        const openBtn = floatWindow.querySelector('#gm-btn-open');
        if (openBtn) {
            const off = c.found === 0;
            openBtn.classList.toggle('gm-disabled', off);
            openBtn.setAttribute('aria-disabled', off ? 'true' : 'false');
        }
        const hideBtn = floatWindow.querySelector('#gm-btn-hide');
        if (hideBtn) {
            hideBtn.textContent = hideMode ? '恢复' : '隐藏';
            hideBtn.classList.toggle('gm-disabled', !hideMode && c.none === 0);
        }
    }

    /** 头部进度：仅在检测中 / 暂停时显示，位置在数量按钮右侧 */
    function updateProgressBar() {
        if (!floatWindow) return;
        const wrap = floatWindow.querySelector('#gm-progress');
        if (!wrap) return;

        const total = progTotal;
        const done = Math.min(progDone, total);
        const visible = total > 0 && (isChecking || checkPaused);
        const display = visible ? 'flex' : 'none';
        if (wrap.style.display !== display) wrap.style.display = display;
        if (!visible) return;

        const pct = total ? Math.round((done / total) * 100) : 0;
        wrap.classList.toggle('gm-paused', checkPaused);

        const bar = wrap.querySelector('#gm-progress-bar');
        if (bar) bar.style.width = `${pct}%`;

        const text = wrap.querySelector('#gm-progress-text');
        const next = `${checkPaused ? '已暂停' : '检测'} ${done}/${total} · ${pct}%`;
        if (text && text.textContent !== next) text.textContent = next;
    }

    function progressTip() {
        const total = Math.max(progTotal, progDone);
        const done = Math.min(progDone, total);
        return `${checkPaused ? '已暂停' : '检测中'}：${done}/${total}（${total ? Math.round(done / total * 100) : 0}%）\n` +
            `每批 ${CONFIG.CHECK_CONCURRENCY} 个并发，批间隔 ${CONFIG.CHECK_BATCH_WAIT_MS}ms\n` +
            `再次点击「检测/暂停」可继续`;
    }

    /** 缓存软上限：页面翻动很久后清理不在当前页的历史状态 */
    function pruneStatusCache() {
        if (nyaaStatusCache.size <= CONFIG.CACHE_SOFT_LIMIT) return;
        for (const key of nyaaStatusCache.keys()) {
            if (!foundNumbers.has(key)) nyaaStatusCache.delete(key);
        }
    }

    function startMutationObserver() {
        if (observer) return;
        const obsConfig = { childList: true, subtree: true, attributes: true, attributeFilter: ['class'], characterData: true };
        observer = new MutationObserver(mutations => {
            let needExtractNum = false;
            for (const mut of mutations) {
                // 忽略悬浮窗自身的 DOM 变化，避免自触发回环
                if (floatWindow && floatWindow.contains(mut.target)) continue;

                if (mut.type === 'childList') {
                    for (const node of mut.addedNodes) {
                        if (floatWindow && floatWindow.contains(node)) continue;
                        if (node.nodeType === Node.ELEMENT_NODE) {
                            queueElement(node);      // 入队，帧内合并处理
                            needExtractNum = true;
                        } else if (node.nodeType === Node.TEXT_NODE) {
                            queueText(node);
                        }
                    }
                } else if (mut.type === 'characterData') {
                    queueText(mut.target);
                } else if (mut.type === 'attributes') {
                    if (mut.target.tagName === 'IMG') unblurImg(mut.target);
                }
            }
            if (needExtractNum) debouncedExtractNum();
        });
        observer.observe(document.body, obsConfig);
    }

    window.addEventListener('beforeunload', () => { saveSession(); if (observer) observer.disconnect(); });

    function init() {
        restoreSession();              // 先把上一页留下的番号与检测结果接回来
        injectGlobalFonts();
        batchUnblurAllImg();
        startMutationObserver();
        watchUrlChanges();             // 站内 pushState 换列表时，数字必须跟着清空
        queueElement(document.body);   // 首屏翻译/去模糊走统一队列，先让页面绘制一帧
        extractSevenDigitNumbers();
        updateFloatWindow();
        if (restoredCount) toast(`已继承上一页 ${restoredCount} 个番号（共 ${foundNumbers.size} 个）`);
    }

    if (document.readyState === 'loading') { document.addEventListener('DOMContentLoaded', init); }
    else { init(); }
})();
