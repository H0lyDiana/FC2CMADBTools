// ==UserScript==
// @name         FC2CMADBTools
// @namespace    http://tampermonkey.net/
// @version      1.3
// @description  提取7位数字生成对应链接悬浮窗、移除图片模糊、页面自定义翻译。
// @author       AI
// @match        https://fc2cmadb.com/*
// @grant        GM_xmlhttpRequest
// @grant        GM_openInTab
// @connect      sukebei.nyaa.si
// ==/UserScript==

(function() {
    'use strict';

    // ====================== 全局常量配置区 ======================
    const CONFIG = {
        OPEN_DELAY_MS: 1000,
        DEBOUNCE_WAIT: 300,
        FLOAT_WIN_WIDTH: 320,
        FLOAT_WIN_MAX_HEIGHT: 400,
        FLOAT_WIN_ZINDEX: 999999,
        NUMBER_REG: /\b\d{6,7}\b/,
        STORAGE_KEY_WIN_POS: 'fc2cmadb_float_pos',
        CHECK_DELAY_MS: 1500 // 队列检测间隔，1秒1个保护IP
    };

    const translationDict = {
        "ランキング": "排行", "コメントする": "发表评论", "セール": "折扣",
        "コメント": "评论", "お気に入り": "收藏", "女優": "女优",
        "販売者": "作者", "タイトル ID": "标题ID", "人気作品": "人气作品",
        "すべて見る": "查看全部", "テーマ切り替え": "切换主题",
        "ライトモードに切り替える": "白天模式", "ダークモードに切り替える": "黑暗模式",
        "システムテーマを有効にする": "跟随系统设置",
        "旧サイトのアカウントでログインできます。": "可以用旧网站的账号登录。",
        "评论履歴": "历史评论", "まだ评论はありません": "无评论",
        "アカウント": "账户", "ログアウト": "退出登录", "モザイク": "马赛克",
        "販売日": "销售日期", "収録時間": "收录时间", "タグ": "标签",
        "リンク": "关联", "閉じる": "关闭","検索結果": "搜索结果",
        "表示中": "此页显示", "から": "至","件目": " ",
        "、全": "   总计"
    };

    let foundNumbers = new Set();
    let floatWindow = null;
    let observer = null;
    let floatHeader = null;
    let cachedBlurImgs = new WeakSet();
    let winDragPos = { left: '', top: '' };

    // ======= 资源有效性检测核心 =======
    const nyaaStatusCache = new Map(); // 状态: 'loading' | 'found' | 'not-found' | 'error' | 'banned'
    const checkQueue = [];
    let isChecking = false;

    // 加入检测队列
    function enqueueCheck(num) {
        if (nyaaStatusCache.has(num)) {
            updateLinkDom(num);
            return;
        }
        nyaaStatusCache.set(num, 'loading');
        checkQueue.push(num);
        updateLinkDom(num);
        processQueue();
    }

    // 异步排队处理请求
    async function processQueue() {
        if (isChecking) return;
        isChecking = true;

        while (checkQueue.length > 0) {
            const num = checkQueue.shift();

            await new Promise(resolve => {
                const url = `https://sukebei.nyaa.si/?f=0&c=0_0&q=${num}`;
                GM_xmlhttpRequest({
                    method: "GET",
                    url: url,
                    anonymous: true,
                    headers: {
                        "User-Agent": navigator.userAgent,
                        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8"
                    },
                    onload: function(response) {
                        if (response.status === 200) {
                            if (response.responseText.includes("No results found")) {
                                nyaaStatusCache.set(num, 'not-found');
                            } else {
                                nyaaStatusCache.set(num, 'found');
                            }
                        } else if (response.status === 429 || response.status === 403) {
                            nyaaStatusCache.set(num, 'banned');
                            checkQueue.length = 0; // 停止队列
                        } else {
                            nyaaStatusCache.set(num, 'error');
                        }
                        updateLinkDom(num);
                        setTimeout(resolve, CONFIG.CHECK_DELAY_MS);
                    },
                    onerror: function() {
                        nyaaStatusCache.set(num, 'error');
                        updateLinkDom(num);
                        setTimeout(resolve, CONFIG.CHECK_DELAY_MS);
                    },
                    ontimeout: function() {
                        nyaaStatusCache.set(num, 'error');
                        updateLinkDom(num);
                        setTimeout(resolve, CONFIG.CHECK_DELAY_MS);
                    }
                });
            });
        }
        isChecking = false;
    }

    /** 动态更新单个链接与检测按钮的 DOM 样式 */
    function updateLinkDom(num) {
        if (!floatWindow) return;
        const status = nyaaStatusCache.get(num);
        const links = floatWindow.querySelectorAll(`a[data-nyaa="${num}"]`);
        const btns = floatWindow.querySelectorAll(`button[data-check="${num}"]`);

        // 更新文字和链接颜色
        links.forEach(link => {
            link.classList.remove('not-found', 'loading', 'error', 'banned');
            let statusText = '';

            if (status === 'not-found') {
                link.classList.add('not-found');
                statusText = '<span style="font-size:11px; margin-left:6px;">[无资源]</span>';
            } else if (status === 'loading') {
                link.classList.add('loading');
                statusText = '<span style="font-size:11px; margin-left:6px;">[检测中]</span>';
            } else if (status === 'error') {
                link.classList.add('error');
                statusText = '<span style="font-size:11px; margin-left:6px;">[网络错误]</span>';
            } else if (status === 'banned') {
                link.classList.add('banned');
                statusText = '<span style="font-size:11px; margin-left:6px;">[请求频繁]</span>';
            }
            // found 状态不加文字保持清爽
            link.innerHTML = `${num}${statusText}`;
        });

        // 更新旁边的小按钮状态
        btns.forEach(btn => {
            if (status === 'loading') {
                btn.disabled = true;
                btn.innerText = '...';
            } else {
                // 如果已经有确定结果了，直接隐藏该按钮
                btn.style.display = 'none';
            }
        });
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

    function saveWindowPosition(left, top) { localStorage.setItem(CONFIG.STORAGE_KEY_WIN_POS, JSON.stringify({ left, top })); }
    function loadWindowPosition() {
        const posStr = localStorage.getItem(CONFIG.STORAGE_KEY_WIN_POS);
        return posStr ? JSON.parse(posStr) : null;
    }

    function injectGlobalFonts() {
        if (document.getElementById('gm-global-font-style')) return;
        const fontStyle = document.createElement('style');
        fontStyle.id = 'gm-global-font-style';
        fontStyle.innerHTML = `
            body, div, p, span, a, td, th, input, button, textarea, section, article, li, ul, ol, h1, h2, h3, h4, h5, h6 {
                font-family: "Microsoft YaHei", "微软雅黑", -apple-system, BlinkMacSystemFont, sans-serif !important;
            }
            #gm-helper-float-window, #gm-helper-float-window * { font-family: "Microsoft YaHei", "微软雅黑", sans-serif !important; }
        `;
        document.head.appendChild(fontStyle);
    }

    function translateTextNode(node) {
        if (!node?.nodeValue?.trim()) return;
        let text = node.nodeValue; let isChanged = false;
        for (const [raw, target] of Object.entries(translationDict)) {
            if (text.includes(raw)) { text = text.split(raw).join(target); isChanged = true; }
        }
        if (isChanged) node.nodeValue = text;
    }

    function translateAttributes(el) {
        if (el.nodeType !== Node.ELEMENT_NODE) return;
        const transAttrs = ['title', 'alt', 'aria-label', 'placeholder', 'data-tip', 'data-tooltip'];
        transAttrs.forEach(attr => {
            if (!el.hasAttribute(attr)) return;
            let val = el.getAttribute(attr); let newVal = val;
            for (const [raw, target] of Object.entries(translationDict)) { newVal = newVal.split(raw).join(target); }
            if (newVal !== val) el.setAttribute(attr, newVal);
        });
    }

    function translateElement(rootEl) {
        if (!rootEl || ['SCRIPT','STYLE','TEXTAREA','NOSCRIPT','IFRAME'].includes(rootEl.tagName)) return;
        translateAttributes(rootEl);
        rootEl.querySelectorAll('*').forEach(el => {
            if (!['SCRIPT','STYLE','TEXTAREA','NOSCRIPT','IFRAME'].includes(el.tagName)) translateAttributes(el);
        });
        const walker = document.createTreeWalker(rootEl, NodeFilter.SHOW_TEXT,
            { acceptNode: n => n.nodeValue.trim() ? NodeFilter.FILTER_ACCEPT : NodeFilter.FILTER_REJECT }, false);
        let textNode;
        while ((textNode = walker.nextNode())) translateTextNode(textNode);
    }

    function unblurImg(imgEl) {
        if (!imgEl || cachedBlurImgs.has(imgEl)) return;
        cachedBlurImgs.add(imgEl);
        const blurClassList = Array.from(imgEl.classList).filter(c => c.startsWith('blur'));
        blurClassList.forEach(cls => imgEl.classList.remove(cls));
        imgEl.classList.add('null');
        imgEl.style.filter = 'none !important';
        imgEl.style.backdropFilter = 'none !important';
    }

    function batchUnblurAllImg() { document.querySelectorAll('img[class*="blur"]').forEach(unblurImg); }

    function extractSevenDigitNumbers() {
        const prevNums = new Set(foundNumbers);
        foundNumbers.clear();

        const targetSpans = document.querySelectorAll('span.absolute.top-0.left-0.text-sm.text-white.bg-gray-800.opacity-80.rounded-tl-lg.px-1');
        const targetTds = document.querySelectorAll('td.w-8\\/10.text-base.font-medium');

        targetSpans.forEach(span => {
            const match = span.textContent.match(CONFIG.NUMBER_REG);
            if (match) foundNumbers.add(match[0]);
        });
        targetTds.forEach(td => {
            const match = td.textContent.match(CONFIG.NUMBER_REG);
            if (match) foundNumbers.add(match[0]);
        });

        let isChanged = (foundNumbers.size !== prevNums.size);
        if (!isChanged) {
            for (let num of foundNumbers) { if (!prevNums.has(num)) { isChanged = true; break; } }
        }
        if (isChanged) updateFloatWindow();
    }
    const debouncedExtractNum = debounce(extractSevenDigitNumbers, CONFIG.DEBOUNCE_WAIT);

    function createFloatWindowStyle() {
        if (document.getElementById('gm-float-win-style')) return;
        const style = document.createElement('style');
        style.id = 'gm-float-win-style';
        style.innerHTML = `
            #gm-helper-float-window {
                position: fixed; right: 20px; top: 100px;
                z-index: ${CONFIG.FLOAT_WIN_ZINDEX}; min-width: ${CONFIG.FLOAT_WIN_WIDTH}px;
                background: #fff; border: 1px solid #ccc;
                box-shadow: 0 4px 12px rgba(0,0,0,0.15); border-radius: 8px;
                font-size: 14px; color: #333; overflow: hidden;
            }
            #gm-helper-header {
                padding: 10px; background: #f5f5f5; border-bottom: 1px solid #ddd;
                cursor: move; display: flex; justify-content: space-between; align-items: center; user-select: none;
            }
            #gm-helper-body { max-height: ${CONFIG.FLOAT_WIN_MAX_HEIGHT}px; overflow-y: auto; padding: 10px; }
            #gm-helper-body::-webkit-scrollbar { width: 6px; }
            #gm-helper-body::-webkit-scrollbar-thumb { background: #aaa; border-radius: 3px; }
            .gm-btn { padding: 4px 8px; cursor: pointer; border: 1px solid #ccc; background: #fff; border-radius: 4px; font-size:12px; }
            .gm-btn:hover:not(:disabled) { background: #e9e9e9; }
            .gm-btn:disabled { background: #f0f0f0; color: #999; cursor: not-allowed; }

            /* 单个检测小按钮样式 */
            .gm-check-btn {
                margin-left: 8px; padding: 2px 6px; font-size: 11px; cursor: pointer;
                border: 1px solid #3498db; background: #fff; color: #3498db; border-radius: 4px;
            }
            .gm-check-btn:hover:not(:disabled) { background: #3498db; color: #fff; }
            .gm-check-btn:disabled { border-color: #bdc3c7; color: #7f8c8d; background: #ecf0f1; cursor: not-allowed; }

            #gm-helper-close { cursor: pointer; color: red; font-weight: bold; font-size: 16px; margin-left: 10px; }
            .gm-table { width: 100%; border-collapse: collapse; text-align: center; }
            .gm-table th, .gm-table td { border: 1px solid #eee; padding: 6px; vertical-align: middle; }
            .gm-link { color: #0066cc; text-decoration: none; cursor: pointer; font-weight: bold; transition: color 0.2s; }
            .gm-link:hover { text-decoration: underline; color: #004499; }

            /* 状态颜色标记 */
            .gm-link.not-found { color: #e74c3c !important; text-decoration: line-through; }
            .gm-link.not-found:hover { color: #c0392b !important; }
            .gm-link.loading { color: #95a5a6 !important; font-weight: normal; }
            .gm-link.error { color: #f39c12 !important; }
            .gm-link.banned { color: #8e44ad !important; }
        `;
        document.head.appendChild(style);
    }

    function createFloatWindow() {
        if (document.getElementById('gm-helper-float-window')) return;
        createFloatWindowStyle();

        floatWindow = document.createElement('div');
        floatWindow.id = 'gm-helper-float-window';
        floatHeader = document.createElement('div');
        floatHeader.id = 'gm-helper-header';
        floatHeader.innerHTML = `
            <div>
                <strong id="gm-count-display">找到 0 个</strong>
                <button class="gm-btn" id="gm-btn-refresh" style="margin-left:5px;">刷新</button>
                <button class="gm-btn" id="gm-btn-check-all" style="margin-left:5px;">一键判断</button>
            </div>
            <div id="gm-helper-close">×</div>
        `;
        const bodyWrap = document.createElement('div');
        bodyWrap.id = 'gm-helper-body';
        bodyWrap.innerHTML = `
            <table class="gm-table">
                <thead><tr><th>下载链接</th><th>在线播放</th></tr></thead>
                <tbody id="gm-table-body"></tbody>
            </table>
        `;
        floatWindow.append(floatHeader, bodyWrap);
        document.body.appendChild(floatWindow);

        const lastPos = loadWindowPosition();
        if (lastPos) { floatWindow.style.left = lastPos.left; floatWindow.style.top = lastPos.top; floatWindow.style.right = 'auto'; }

        // 事件委托：处理 链接点击 和 检测按钮点击
        floatWindow.addEventListener('click', e => {
            const link = e.target.closest('.gm-link');
            if (link) {
                e.preventDefault();
                safeOpenTab(link.getAttribute('href'));
                setTimeout(() => window.focus(), 50);
                return;
            }

            const checkBtn = e.target.closest('.gm-check-btn');
            if (checkBtn && !checkBtn.disabled) {
                const num = checkBtn.getAttribute('data-check');
                if (num) enqueueCheck(num);
            }
        });

        document.getElementById('gm-helper-close').onclick = () => { floatWindow.style.display = 'none'; };

        document.getElementById('gm-btn-refresh').onclick = () => {
            batchUnblurAllImg(); translateElement(document.body);
            extractSevenDigitNumbers(); floatWindow.style.display = 'block'; updateFloatWindow();
        };

        // 一键判断（将所有未检测的推入队列）
        const checkAllBtn = document.getElementById('gm-btn-check-all');
        checkAllBtn.onclick = function() {
            const numList = Array.from(foundNumbers).sort((a,b) => a - b);
            let addedCount = 0;
            numList.forEach(num => {
                // 只有还没有检测缓存的才加入队列
                if (!nyaaStatusCache.has(num)) {
                    enqueueCheck(num);
                    addedCount++;
                }
            });
            if (addedCount > 0) {
                const originText = this.innerText;
                this.innerText = `排队中(${addedCount})`;
                setTimeout(() => { this.innerText = originText; }, 1500);
            }
        };

        floatHeader.onmousedown = dragStart;
    }

    function dragStart(e) {
        if (['BUTTON', 'DIV'].includes(e.target.tagName) && e.target.id !== 'gm-helper-header') return;
        e.preventDefault();
        const rect = floatWindow.getBoundingClientRect();
        const shiftX = e.clientX - rect.left, shiftY = e.clientY - rect.top;

        function moveHandler(evt) {
            let x = evt.clientX - shiftX, y = evt.clientY - shiftY;
            const winW = window.innerWidth, winH = window.innerHeight;
            const boxW = floatWindow.offsetWidth, boxH = floatWindow.offsetHeight;
            if (x < 0) x = 0; if (y < 0) y = 0;
            if (x + boxW > winW) x = winW - boxW; if (y + boxH > winH) y = winH - boxH;
            floatWindow.style.left = `${x}px`; floatWindow.style.top = `${y}px`; floatWindow.style.right = 'auto';
            winDragPos.left = `${x}px`; winDragPos.top = `${y}px`;
        }
        function upHandler() {
            document.removeEventListener('mousemove', moveHandler);
            document.removeEventListener('mouseup', upHandler);
            saveWindowPosition(winDragPos.left, winDragPos.top);
        }
        document.addEventListener('mousemove', moveHandler);
        document.addEventListener('mouseup', upHandler, { once: true });
    }

    function updateFloatWindow() {
        if (!floatWindow) createFloatWindow();
        floatWindow.style.display = 'block';

        const tbody = document.getElementById('gm-table-body');
        const countText = document.getElementById('gm-count-display');
        tbody.innerHTML = '';
        const numArr = Array.from(foundNumbers).sort((a,b) => a - b);
        countText.innerText = `找到 ${numArr.length} 个`;

        numArr.forEach(num => {
            const tr = document.createElement('tr');
            const nyaaUrl = `https://sukebei.nyaa.si/?f=0&c=0_0&q=${num}`;
            const supjavUrl = `https://supjav.com/zh/?s=${num}`;

            // 初始化读取缓存渲染（例如由于窗口拖拽、刷新等引发的重绘，保留上次的按钮状态）
            const status = nyaaStatusCache.get(num);
            let extraClass = '';
            let statusText = '';
            let btnStyle = '';

            if (status) {
                btnStyle = (status === 'loading') ? '' : 'display:none;';
                if (status === 'not-found') {
                    extraClass = 'not-found';
                    statusText = '<span style="font-size:11px; margin-left:6px;">[无资源]</span>';
                } else if (status === 'error') { extraClass = 'error'; statusText = '<span style="font-size:11px; margin-left:6px;">[网络错误]</span>'; }
                else if (status === 'banned') { extraClass = 'banned'; statusText = '<span style="font-size:11px; margin-left:6px;">[请求频繁]</span>'; }
                else if (status === 'loading') { extraClass = 'loading'; statusText = '<span style="font-size:11px; margin-left:6px;">[检测中]</span>'; }
            }

            const td1 = document.createElement('td');
            // 将超链接和手动检测按钮放在同一格
            td1.innerHTML = `
                <a href="${nyaaUrl}" class="gm-link ${extraClass}" data-nyaa="${num}">${num}${statusText}</a>
                <button class="gm-check-btn" data-check="${num}" style="${btnStyle}">检测</button>
            `;
            // 若正在加载，顺便禁用重绘的按钮
            if (status === 'loading') {
                const btn = td1.querySelector('button');
                if (btn) { btn.disabled = true; btn.innerText = '...'; }
            }

            const td2 = document.createElement('td');
            td2.innerHTML = `<a href="${supjavUrl}" class="gm-link">${num}</a>`;

            tr.append(td1, td2);
            tbody.appendChild(tr);

            // 注意：此处已经移除了强制 enqueueCheck(num) 的自动执行
        });
    }

    function startMutationObserver() {
        if (observer) return;
        const obsConfig = { childList: true, subtree: true, attributes: true, attributeFilter: ['class'], characterData: true };
        observer = new MutationObserver(mutations => {
            let needExtractNum = false;
            mutations.forEach(mut => {
                if (mut.type === 'childList') {
                    mut.addedNodes.forEach(node => {
                        if (node.nodeType === Node.TEXT_NODE) translateTextNode(node);
                        else if (node.nodeType === Node.ELEMENT_NODE) {
                            translateElement(node);
                            if (node.tagName === 'IMG') unblurImg(node);
                            node.querySelectorAll('img[class*="blur"]').forEach(unblurImg);
                            needExtractNum = true;
                        }
                    });
                }
                if (mut.type === 'characterData') translateTextNode(mut.target);
                if (mut.type === 'attributes') {
                    if (mut.attributeName === 'class' && mut.target.tagName === 'IMG') unblurImg(mut.target);
                }
            });
            if (needExtractNum) debouncedExtractNum();
        });
        observer.observe(document.body, obsConfig);
    }

    window.addEventListener('beforeunload', () => { if (observer) observer.disconnect(); });

    function init() {
        injectGlobalFonts(); batchUnblurAllImg(); translateElement(document.body);
        extractSevenDigitNumbers(); updateFloatWindow(); startMutationObserver();
    }

    if (document.readyState === 'loading') { document.addEventListener('DOMContentLoaded', init); }
    else { init(); }
})();
