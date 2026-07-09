// ==UserScript==
// @name         FC2CMADBTools
// @namespace    http://tampermonkey.net/
// @version      2.0
// @description  提取7位数字生成对应链接悬浮窗、移除图片模糊、页面自定义翻译。
// @author       AI
// @match        https://fc2cmadb.com/*
// @grant        none
// ==/UserScript==


(function() {
    'use strict';

    // ====================== 全局常量配置区（统一修改无需翻代码） ======================
    const CONFIG = {
        OPEN_DELAY_MS: 1000,
        DEBOUNCE_WAIT: 300,
        FLOAT_WIN_WIDTH: 280,
        FLOAT_WIN_MAX_HEIGHT: 400,
        FLOAT_WIN_ZINDEX: 999999,
        NUMBER_REG: /\b\d{6,7}\b/,
        STORAGE_KEY_WIN_POS: 'fc2cmadb_float_pos'
    };

    // 翻译词典 - 可自由扩充
    const translationDict = {
        "ランキング": "排行",
        "コメントする": "发表评论",
        "セール": "折扣",
        "コメント": "评论",
        "お気に入り": "收藏",
        "女優": "女优",
        "販売者": "作者",
        "タイトル ID": "标题ID",
        "人気作品": "人气作品",
        "すべて見る": "查看全部",
        "テーマ切り替え": "切换主题",
        "ライトモードに切り替える": "白天模式",
        "ダークモードに切り替える": "黑暗模式",
        "システムテーマを有効にする": "跟随系统设置",
        "旧サイトのアカウントでログインできます。": "可以用旧网站的账号登录。",
        "评论履歴": "历史评论",
        "まだ评论はありません": "无评论",
        "アカウント": "账户",
        "ログアウト": "退出登录",
        "モザイク": "马赛克",
        "販売日": "销售日期",
        "収録時間": "收录时间",
        "タグ": "标签",
        "リンク": "关联",
        "閉じる": "关闭",
    };

    // 全局变量
    let foundNumbers = new Set();
    let floatWindow = null;
    let observer = null;
    let floatHeader = null;
    let cachedBlurImgs = new WeakSet(); // 缓存已处理去模糊图片，避免重复操作
    let winDragPos = { left: '', top: '' };

    // ====================== 工具函数 ======================
    /** 防抖封装 */
    function debounce(func, wait) {
        let timeoutId = null;
        return function(...args) {
            clearTimeout(timeoutId);
            timeoutId = setTimeout(() => func.apply(this, args), wait);
        };
    }

    /** 安全打开新标签，兼容GM函数兜底 */
    function safeOpenTab(url) {
        try {
            GM_openInTab(url, { active: false, insert: true, setParent: true });
        } catch (err) {
            window.open(url, '_blank');
        }
    }

    /** 保存悬浮窗位置到本地存储 */
    function saveWindowPosition(left, top) {
        localStorage.setItem(CONFIG.STORAGE_KEY_WIN_POS, JSON.stringify({ left, top }));
    }

    /** 读取悬浮窗上次位置 */
    function loadWindowPosition() {
        const posStr = localStorage.getItem(CONFIG.STORAGE_KEY_WIN_POS);
        if (!posStr) return null;
        try {
            return JSON.parse(posStr);
        } catch {
            return null;
        }
    }

    // ====================== 1. 全局字体注入 ======================
    function injectGlobalFonts() {
        if (document.getElementById('gm-global-font-style')) return;
        const fontStyle = document.createElement('style');
        fontStyle.id = 'gm-global-font-style';
        fontStyle.innerHTML = `
            body, div, p, span, a, td, th, input, button, textarea, section, article, li, ul, ol, h1, h2, h3, h4, h5, h6 {
                font-family: "Microsoft YaHei", "微软雅黑", -apple-system, BlinkMacSystemFont, sans-serif !important;
            }
            #gm-helper-float-window, #gm-helper-float-window * {
                font-family: "Microsoft YaHei", "微软雅黑", sans-serif !important;
            }
        `;
        document.head.appendChild(fontStyle);
    }

    // ====================== 2. 翻译模块（性能优化版） ======================
    /** 翻译文本节点 */
    function translateTextNode(node) {
        if (!node?.nodeValue?.trim()) return;
        let text = node.nodeValue;
        let isChanged = false;

        for (const [raw, target] of Object.entries(translationDict)) {
            if (text.includes(raw)) {
                text = text.split(raw).join(target);
                isChanged = true;
            }
        }

        if (isChanged) node.nodeValue = text;
    }

    /** 翻译元素属性 */
    function translateAttributes(el) {
        if (el.nodeType !== Node.ELEMENT_NODE) return;
        const transAttrs = ['title', 'alt', 'aria-label', 'placeholder', 'data-tip', 'data-tooltip'];
        transAttrs.forEach(attr => {
            if (!el.hasAttribute(attr)) return;
            let val = el.getAttribute(attr);
            let newVal = val;
            for (const [raw, target] of Object.entries(translationDict)) {
                newVal = newVal.split(raw).join(target);
            }
            if (newVal !== val) el.setAttribute(attr, newVal);
        });
    }

    /** 批量翻译元素及其内部所有文本/属性 */
    function translateElement(rootEl) {
        if (!rootEl || ['SCRIPT','STYLE','TEXTAREA','NOSCRIPT','IFRAME'].includes(rootEl.tagName)) return;
        translateAttributes(rootEl);

        // 遍历所有后代元素翻译属性
        rootEl.querySelectorAll('*').forEach(el => {
            if (!['SCRIPT','STYLE','TEXTAREA','NOSCRIPT','IFRAME'].includes(el.tagName)) {
                translateAttributes(el);
            }
        });

        // 遍历所有文本节点翻译文字
        const walker = document.createTreeWalker(
            rootEl,
            NodeFilter.SHOW_TEXT,
            { acceptNode: n => n.nodeValue.trim() ? NodeFilter.FILTER_ACCEPT : NodeFilter.FILTER_REJECT },
            false
        );
        let textNode;
        while ((textNode = walker.nextNode())) translateTextNode(textNode);
    }

    // ====================== 3. 图片去模糊模块（强制兜底样式） ======================
    function unblurImg(imgEl) {
        if (!imgEl || cachedBlurImgs.has(imgEl)) return;
        cachedBlurImgs.add(imgEl);

        // 移除所有blur前缀类名
        const blurClassList = Array.from(imgEl.classList).filter(c => c.startsWith('blur'));
        blurClassList.forEach(cls => imgEl.classList.remove(cls));
        imgEl.classList.add('null');

        // 强制清除滤镜，兜底样式防止页面JS重新加blur
        imgEl.style.filter = 'none !important';
        imgEl.style.backdropFilter = 'none !important';
    }

    // 批量处理页面所有模糊图片
    function batchUnblurAllImg() {
        document.querySelectorAll('img[class*="blur"]').forEach(unblurImg);
    }

    // ====================== 4. 7位数字提取模块 ======================
    function extractSevenDigitNumbers() {
        const prevCount = foundNumbers.size;
        foundNumbers.clear();

        // 精准限定目标DOM，不全局遍历所有span/td，提升性能
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

        // 数字发生变化才更新悬浮窗
        if (foundNumbers.size !== prevCount) updateFloatWindow();
    }
    const debouncedExtractNum = debounce(extractSevenDigitNumbers, CONFIG.DEBOUNCE_WAIT);

    // ====================== 5. 悬浮窗UI 创建/更新/拖拽 ======================
    function createFloatWindowStyle() {
        if (document.getElementById('gm-float-win-style')) return;
        const style = document.createElement('style');
        style.id = 'gm-float-win-style';
        style.innerHTML = `
            #gm-helper-float-window {
                position: fixed;
                right: 20px;
                top: 100px;
                z-index: ${CONFIG.FLOAT_WIN_ZINDEX};
                min-width: ${CONFIG.FLOAT_WIN_WIDTH}px;
                background: #fff;
                border: 1px solid #ccc;
                box-shadow: 0 4px 12px rgba(0,0,0,0.15);
                border-radius: 8px;
                font-size: 14px;
                color: #333;
                overflow: hidden;
            }
            #gm-helper-header {
                padding: 10px;
                background: #f5f5f5;
                border-bottom: 1px solid #ddd;
                border-top-left-radius: 8px;
                border-top-right-radius: 8px;
                cursor: move;
                display: flex;
                justify-content: space-between;
                align-items: center;
                user-select: none;
            }
            #gm-helper-body {
                max-height: ${CONFIG.FLOAT_WIN_MAX_HEIGHT}px;
                overflow-y: auto;
                padding: 10px;
            }
            #gm-helper-body::-webkit-scrollbar { width: 6px; }
            #gm-helper-body::-webkit-scrollbar-thumb { background: #aaa; border-radius: 3px; }
            .gm-btn {
                padding: 4px 8px;
                cursor: pointer;
                border: 1px solid #ccc;
                background: #fff;
                border-radius: 4px;
                font-size:12px;
            }
            .gm-btn:hover:not(:disabled) { background: #e9e9e9; }
            .gm-btn:disabled { background: #f0f0f0; color: #999; cursor: not-allowed; }
            #gm-helper-close {
                cursor: pointer;
                color: red;
                font-weight: bold;
                font-size: 16px;
                margin-left: 10px;
            }
            .gm-table { width: 100%; border-collapse: collapse; text-align: center; }
            .gm-table th, .gm-table td { border: 1px solid #eee; padding: 6px; }
            .gm-link { color: #0066cc; text-decoration: none; cursor: pointer; font-weight: bold; }
            .gm-link:hover { text-decoration: underline; color: #004499; }
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
                <button class="gm-btn" id="gm-btn-open-all" style="margin-left:5px;">一键打开</button>
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

        // 恢复上次拖拽位置
        const lastPos = loadWindowPosition();
        if (lastPos) {
            floatWindow.style.left = lastPos.left;
            floatWindow.style.top = lastPos.top;
            floatWindow.style.right = 'auto';
        }

        // 链接点击跳转
        floatWindow.addEventListener('click', e => {
            const link = e.target.closest('.gm-link');
            if (!link) return;
            e.preventDefault();
            safeOpenTab(link.getAttribute('href'));
            setTimeout(() => window.focus(), 50);
        });

        // 关闭按钮
        document.getElementById('gm-helper-close').onclick = () => {
            floatWindow.style.display = 'none';
        };

        // 刷新按钮
        document.getElementById('gm-btn-refresh').onclick = () => {
            batchUnblurAllImg();
            translateElement(document.body);
            extractSevenDigitNumbers();
            floatWindow.style.display = 'block';
            updateFloatWindow();
        };

        // 一键打开全部
        const openAllBtn = document.getElementById('gm-btn-open-all');
        openAllBtn.onclick = async function() {
            const btn = this;
            const numList = Array.from(foundNumbers).sort((a,b) => a - b);
            if (!numList.length) return;
            if (btn.disabled) return;

            btn.disabled = true;
            const originText = btn.innerText;

            for (let i = 0; i < numList.length; i++) {
                const num = numList[i];
                const nyaaUrl = `https://sukebei.nyaa.si/?f=0&c=0_0&q=${num}`;
                btn.innerText = `打开中 (${i + 1}/${numList.length})`;
                safeOpenTab(nyaaUrl);
                window.focus();
                if (i < numList.length - 1) await new Promise(r => setTimeout(r, CONFIG.OPEN_DELAY_MS));
            }

            btn.innerText = '完成!';
            setTimeout(() => {
                btn.disabled = false;
                btn.innerText = originText;
                window.focus();
            }, 1500);
        };

        // 拖拽逻辑（边界限制+保存位置）
        floatHeader.onmousedown = dragStart;
    }

    function dragStart(e) {
        // 排除按钮/关闭区域，不触发拖拽
        if (['BUTTON', 'DIV'].includes(e.target.tagName) && e.target.id !== 'gm-helper-header') return;
        e.preventDefault();
        const rect = floatWindow.getBoundingClientRect();
        const shiftX = e.clientX - rect.left;
        const shiftY = e.clientY - rect.top;

        function moveHandler(evt) {
            // 边界限制，窗口不超出可视区域
            let x = evt.clientX - shiftX;
            let y = evt.clientY - shiftY;
            const winW = window.innerWidth;
            const winH = window.innerHeight;
            const boxW = floatWindow.offsetWidth;
            const boxH = floatWindow.offsetHeight;

            if (x < 0) x = 0;
            if (y < 0) y = 0;
            if (x + boxW > winW) x = winW - boxW;
            if (y + boxH > winH) y = winH - boxH;

            floatWindow.style.left = `${x}px`;
            floatWindow.style.top = `${y}px`;
            floatWindow.style.right = 'auto';
            winDragPos.left = `${x}px`;
            winDragPos.top = `${y}px`;
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

            const td1 = document.createElement('td');
            td1.innerHTML = `<a href="${nyaaUrl}" class="gm-link">${num}</a>`;
            const td2 = document.createElement('td');
            td2.innerHTML = `<a href="${supjavUrl}" class="gm-link">${num}</a>`;
            tr.append(td1, td2);
            tbody.appendChild(tr);
        });
    }

    // ====================== 6. 页面动态监听 Observer ======================
    function startMutationObserver() {
        if (observer) return;
        const obsConfig = {
            childList: true,
            subtree: true,
            attributes: true,
            attributeFilter: ['class', 'title', 'alt', 'aria-label', 'placeholder', 'data-tip', 'data-tooltip'],
            characterData: true
        };

        observer = new MutationObserver(mutations => {
            let needExtractNum = false;
            let needFullTranslate = false;

            mutations.forEach(mut => {
                // 新增节点
                if (mut.type === 'childList') {
                    mut.addedNodes.forEach(node => {
                        if (node.nodeType === Node.TEXT_NODE) {
                            translateTextNode(node);
                        } else if (node.nodeType === Node.ELEMENT_NODE) {
                            translateElement(node);
                            if (node.tagName === 'IMG') unblurImg(node);
                            node.querySelectorAll('img[class*="blur"]').forEach(unblurImg);
                            needExtractNum = true;
                        }
                    });
                }
                // 文字内容修改
                if (mut.type === 'characterData') translateTextNode(mut.target);
                // 属性修改
                if (mut.type === 'attributes') {
                    const target = mut.target;
                    if (mut.attributeName === 'class' && target.tagName === 'IMG') {
                        unblurImg(target);
                    } else translateAttributes(target);
                }
            });

            if (needExtractNum) debouncedExtractNum();
        });
        observer.observe(document.body, obsConfig);
    }

    // 页面卸载销毁监听，防止内存泄漏
    window.addEventListener('beforeunload', () => {
        if (observer) observer.disconnect();
    });

    // ====================== 7. 脚本初始化入口 ======================
    function init() {
        injectGlobalFonts();
        batchUnblurAllImg();
        translateElement(document.body);
        extractSevenDigitNumbers();
        updateFloatWindow();
        startMutationObserver();
    }

    // DOM加载完成执行初始化
    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', init);
    } else {
        init();
    }
})();
