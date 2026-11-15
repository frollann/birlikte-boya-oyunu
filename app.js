// ===================== Birlikte Çiz =====================
// Çizgiler piksel değil NOKTA LİSTESİ olarak tutulur; ekran her zoom'da yeniden çizilir (keskin).
const $ = (id) => document.getElementById(id);

const viewport = $('viewport');
const container = $('canvas-container');      // beyaz kağıt (CSS ile ölçeklenir)
const paintCanvas = $('paintCanvas');         // kalıcı çizgiler
const activeCanvas = $('activeCanvas');       // benim devam eden çizgim
const remoteCanvas = $('remoteCanvas');       // karşı tarafın devam eden çizgisi
const templateCanvas = $('templateCanvas');   // şablon çizgileri
const layers = [paintCanvas, activeCanvas, remoteCanvas, templateCanvas];
const cursorEl = $('remote-cursor');          // karşı tarafın imleci
const paintCtx = paintCanvas.getContext('2d');
const activeCtx = activeCanvas.getContext('2d');
const remoteCtx = remoteCanvas.getContext('2d');
const templateCtx = templateCanvas.getContext('2d');

let peer, conn;
let myRole = 'h';                 // 'h' = oda kuran, 'g' = katılan
let currentMode = 'pen', currentColor = '#ec4899', currentSize = 5;

// Tuval (mantıksal koordinatlar) ve görünüm
let LW = 600, LH = 600;
let scale = 1, panX = 0, panY = 0, dpr = 1, cssW = 0, cssH = 0;
let renderedView = { scale: 1, panX: 0, panY: 0 };
let lastRenderMs = 0, rafId = 0, renderTimer = 0, viewOverride = null;

// Çizgiler: {id, owner, color, size, mode, pts:[x0,y0,x1,y1,...]}
let strokes = [], myRedo = [], strokeCounter = 0;
let myStroke = null, remoteStroke = null, isDrawing = false, lastRaw = null;
let remoteCursor = null, cursorTimer = 0, lastCursorSent = 0;
let pending = [], flushTimer = null;

let isPanning = false, startX = 0, startY = 0, isSpacePressed = false;
const pointers = new Map();
let pinch = null;

const EDGE_PASSES = 2;            // kenarlar için çizgi kaç kez çizilsin (1-3)
const MIN_ZOOM = 0.05, MAX_ZOOM = 16;
const MIN_CANVAS = 200, MAX_CANVAS = 4000;   // özel tuval boyutu sınırları
const SMOOTH = 0.45;           // el titremesini yumuşatma (1 = yok, düşük = daha yumuşak)
const MAX_LAYER_PIXELS = 4e6;     // katman başına en fazla piksel (bellek koruması)
const MAX_TEMPLATE_DIM = matchMedia('(pointer: coarse)').matches ? 2400 : 4000;
const LOGICAL_MAX = 1000;
const CHUNK = 16000;
let currentTemplate = null, templateSrc = null;
const tplBuffers = {};
let pendingAction = null;      // karşı taraftan onay beklenen işlem
let templateMips = [];         // şablonun küçültülmüş kopyaları (uzaktan net görünüm)
let confirmResolve = null;

const r1 = (v) => Math.round(v * 10) / 10;
const send = (m) => { if (conn && conn.open) conn.send(m); };

// ---------- Araçlar ----------
$('sizePicker').addEventListener('input', (e) => {
    currentSize = Number(e.target.value);
    $('sizeValue').innerText = currentSize;
});

function setMode(mode) {
    currentMode = mode;
    const base = "px-3 py-2 sm:py-1 rounded-lg font-bold transition ";
    const on = "bg-pink-600 text-white", off = "text-slate-400 hover:text-white";
    $('btn-pen').className = base + (mode === 'pen' ? on : off);
    $('btn-eraser').className = base + (mode === 'eraser' ? on : off);
    $('btn-pan').className = base + (mode === 'pan' ? on : off);
    viewport.style.cursor = mode === 'pan' ? 'grab' : 'crosshair';
}

const PALETTE = ['#000000', '#ef4444', '#f97316', '#facc15', '#22c55e', '#14b8a6',
                 '#3b82f6', '#6366f1', '#a855f7', '#ec4899', '#92400e', '#9ca3af'];

function setColor(c) {
    currentColor = c;
    $('colorPicker').value = c;
    if (currentMode !== 'pen') setMode('pen');
    $('palette').querySelectorAll('button').forEach(b => {
        b.style.outline = b.dataset.color === c.toLowerCase() ? '3px solid #fff' : '';
        b.style.outlineOffset = '1px';
    });
    const cc = $('custom-color');
    cc.style.outline = PALETTE.includes(c.toLowerCase()) ? '' : '3px solid #fff';
    cc.style.outlineOffset = '1px';
    $('fab').style.borderColor = c;
}

function buildPalette() {
    PALETTE.forEach(c => {
        const b = document.createElement('button');
        b.className = 'w-9 h-9 sm:w-6 sm:h-6 rounded-full border-2 border-slate-600';
        b.style.background = c;
        b.dataset.color = c;
        b.setAttribute('aria-label', 'Renk ' + c);
        b.onclick = () => setColor(c);
        $('palette').insertBefore(b, $('custom-color'));
    });
}
$('colorPicker').addEventListener('input', (e) => setColor(e.target.value));
buildPalette();
setColor(currentColor);

// ---------- Menü ve yüzen araç çubuğu (telefon) ----------
function toggleMenu() { $('mobile-menu').classList.toggle('hidden'); }
function closeMenu() { $('mobile-menu').classList.add('hidden'); }
function toggleToolbar() { $('toolbar').classList.toggle('tb-closed'); }
function closeToolbar() { $('toolbar').classList.add('tb-closed'); }
document.addEventListener('pointerdown', (e) => {
    if (!e.target.closest('#mobile-menu, #menu-btn')) closeMenu();
});
viewport.addEventListener('pointerdown', closeToolbar);

// ---------- Görünüm ve çizim motoru ----------
function sizeLayers() {
    cssW = Math.max(1, viewport.clientWidth);
    cssH = Math.max(1, viewport.clientHeight);
    dpr = Math.max(1, Math.min(window.devicePixelRatio || 1, Math.sqrt(MAX_LAYER_PIXELS / (cssW * cssH))));
    layers.forEach(cv => {
        cv.width = Math.round(cssW * dpr);
        cv.height = Math.round(cssH * dpr);
        cv.style.width = cssW + 'px';
        cv.style.height = cssH + 'px';
        cv.style.transformOrigin = '0 0';
    });
}

function applyView(ctx) {
    const v = viewOverride || { a: dpr * scale, tx: dpr * panX, ty: dpr * panY };
    ctx.setTransform(v.a, 0, 0, v.a, v.tx, v.ty);
}

function clearLayer(ctx, cv) {
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.clearRect(0, 0, cv.width, cv.height);
}

const commitOp = (s) => s.mode === 'eraser' ? 'destination-out' : 'source-over';

// Çizginin from. noktasından sonrasını parça parça çizer.
// Önizleme ve kalıcı çizim aynı yöntemi kullandığı için sonuç birebir aynıdır.
function drawSegs(ctx, s, from, op, dot) {
    const p = s.pts, n = p.length / 2;
    if (n < 2 && !(dot && n === 1)) return;
    const erase = s.mode === 'eraser';
    ctx.save();
    applyView(ctx);
    ctx.beginPath(); ctx.rect(0, 0, LW, LH); ctx.clip();   // kağıdın dışına taşma
    ctx.lineCap = ctx.lineJoin = 'round';
    ctx.lineWidth = s.size;
    ctx.globalCompositeOperation = op;
    ctx.strokeStyle = ctx.fillStyle = (erase && op === 'source-over') ? '#ffffff' : s.color;
    if (n === 1) {
        for (let k = 0; k < EDGE_PASSES; k++) { ctx.beginPath(); ctx.arc(p[0], p[1], s.size / 2, 0, Math.PI * 2); ctx.fill(); }
    } else {
        for (let i = Math.max(from, 1); i < n; i++) {
            ctx.beginPath();
            ctx.moveTo(p[2 * i - 2], p[2 * i - 1]);
            ctx.lineTo(p[2 * i], p[2 * i + 1]);
            for (let k = 0; k < EDGE_PASSES; k++) ctx.stroke();
        }
    }
    ctx.restore();
}

function buildMips(src) {
    const mips = [src];
    let c = src, w = src.naturalWidth || src.width, h = src.naturalHeight || src.height;
    while (w > 800) {
        w = Math.round(w / 2); h = Math.round(h / 2);
        const n = document.createElement('canvas');
        n.width = w; n.height = h;
        const x = n.getContext('2d');
        x.imageSmoothingQuality = 'high';
        x.drawImage(c, 0, 0, w, h);
        mips.push(n);
        c = n;
    }
    return mips;
}

// Çok yakın zoom'da şablon kenarları yumuşak görünür; kontrastı artırarak keskinleştirir
function updateTemplateFilter() {
    if (!templateSrc) { templateCanvas.style.filter = ''; return; }
    const srcW = templateSrc.naturalWidth || templateSrc.width;
    const blurPx = scale * LW / srcW;                 // kaynak pikselinin ekrandaki boyu
    const c = Math.min(Math.max(blurPx / 1.5, 1), 10);
    templateCanvas.style.filter = c > 1.1 ? `contrast(${c.toFixed(2)})` : '';
}

function drawTemplate() {
    clearLayer(templateCtx, templateCanvas);
    if (!templateSrc) return;
    const target = LW * scale * dpr;                  // kağıdın ekrandaki piksel genişliği
    let src = templateMips[0] || templateSrc;
    for (let i = templateMips.length - 1; i >= 0; i--) {
        if (templateMips[i].width >= target) { src = templateMips[i]; break; }
    }
    templateCtx.save();
    applyView(templateCtx);
    templateCtx.imageSmoothingEnabled = true;
    templateCtx.imageSmoothingQuality = 'high';
    templateCtx.drawImage(src, 0, 0, LW, LH);
    templateCtx.restore();
}

function renderAll() {
    clearTimeout(renderTimer);
    const t0 = performance.now();
    clearLayer(paintCtx, paintCanvas);
    strokes.forEach(s => drawSegs(paintCtx, s, 0, commitOp(s), true));
    drawTemplate();
    updateTemplateFilter();
    clearLayer(activeCtx, activeCanvas);
    if (myStroke) drawSegs(activeCtx, myStroke, 0, 'source-over', false);
    clearLayer(remoteCtx, remoteCanvas);
    if (remoteStroke) drawSegs(remoteCtx, remoteStroke, 0, 'source-over', false);
    layers.forEach(cv => { cv.style.transform = ''; });
    renderedView = { scale, panX, panY };
    lastRenderMs = performance.now() - t0;
}

function updateRemoteCursor() {
    const c = remoteCursor;
    if (!c) { cursorEl.style.display = 'none'; return; }
    const d = c.mode === 'pan' ? 10 : Math.max(8, c.size * scale);   // halka fırça boyutunda
    cursorEl.style.display = 'block';
    cursorEl.style.width = cursorEl.style.height = d + 'px';
    cursorEl.style.transform = `translate(${panX + c.x * scale - d / 2}px, ${panY + c.y * scale - d / 2}px)`;
    cursorEl.style.borderColor = c.mode === 'eraser' ? '#334155' : c.color;
    cursorEl.style.borderStyle = c.mode === 'eraser' ? 'dashed' : 'solid';
    cursorEl.style.background = c.mode === 'pan' ? c.color : 'transparent';
}

function sendCursor(e) {
    if (!conn || !conn.open || pointers.size > 1) return;
    const now = performance.now();
    if (now - lastCursorSent < 40) return;       // saniyede en fazla ~25 mesaj
    lastCursorSent = now;
    const c = toLogical(e);
    conn.send({ type: 'cursor', x: c.x, y: c.y, size: currentSize, color: currentColor, mode: currentMode });
}

function updatePaper() {
    container.style.width = LW + 'px';
    container.style.height = LH + 'px';
    container.style.transform = `translate(${panX}px, ${panY}px) scale(${scale})`;
    $('zoom-level').innerText = `${Math.round(scale * 100)}%`;
    updateRemoteCursor();
}

// Hareket sırasında eski görüntü CSS ile ölçeklenir, hareket bitince keskin yeniden çizilir
function viewChanged() {
    updatePaper();
    const k = scale / renderedView.scale;
    const tx = panX - k * renderedView.panX, ty = panY - k * renderedView.panY;
    layers.forEach(cv => { cv.style.transform = `translate(${tx}px, ${ty}px) scale(${k})`; });
    if (!rafId) rafId = requestAnimationFrame(() => {
        rafId = 0;
        clearTimeout(renderTimer);
        renderTimer = setTimeout(renderAll, lastRenderMs < 20 ? 0 : 120);
    });
}

function flushView() {
    if (rafId) { cancelAnimationFrame(rafId); rafId = 0; }
    if (paintCanvas.style.transform) renderAll();
}

// ---------- Zoom ----------
function zoomAtPoint(factor, clientX, clientY) {
    const newScale = Math.min(Math.max(scale * factor, MIN_ZOOM), MAX_ZOOM);
    if (newScale === scale) return;
    const rect = viewport.getBoundingClientRect();
    const x = clientX - rect.left, y = clientY - rect.top;
    panX = x - (x - panX) * (newScale / scale);
    panY = y - (y - panY) * (newScale / scale);
    scale = newScale;
    viewChanged();
}
function zoomIn() { const r = viewport.getBoundingClientRect(); zoomAtPoint(1.25, r.left + r.width / 2, r.top + r.height / 2); }
function zoomOut() { const r = viewport.getBoundingClientRect(); zoomAtPoint(0.8, r.left + r.width / 2, r.top + r.height / 2); }

function resetZoom() {
    const w = viewport.clientWidth, h = viewport.clientHeight;
    if (!w || !h || !LW) return;
    if (w !== cssW || h !== cssH) sizeLayers();
    scale = Math.min(w / LW, h / LH) * 0.95;
    panX = (w - LW * scale) / 2;
    panY = (h - LH * scale) / 2;
    updatePaper();
    renderAll();
    container.style.opacity = '1';
}

viewport.addEventListener('wheel', (e) => {
    e.preventDefault();
    zoomAtPoint(e.deltaY < 0 ? 1.15 : 0.85, e.clientX, e.clientY);
}, { passive: false });

let resizeTimer;
const refit = () => { clearTimeout(resizeTimer); resizeTimer = setTimeout(resetZoom, 150); };
window.addEventListener('resize', refit);
window.addEventListener('orientationchange', refit);

// ---------- Klavye ----------
window.addEventListener('keydown', (e) => {
    const typing = document.activeElement && document.activeElement.matches('input:not([type=color]):not([type=range]), textarea');
    if (e.code === 'Space' && !typing && !/INPUT|SELECT/.test(document.activeElement.tagName)) {
        isSpacePressed = true; e.preventDefault();
    }
    if ((e.ctrlKey || e.metaKey) && !isDrawing && !typing) {
        const k = e.key.toLowerCase();
        if (k === 'z' && !e.shiftKey) { e.preventDefault(); undo(); }
        else if (k === 'y' || (k === 'z' && e.shiftKey)) { e.preventDefault(); redo(); }
    }
});
window.addEventListener('keyup', (e) => { if (e.code === 'Space') isSpacePressed = false; });

// ---------- Girdi (fare + dokunma + kalem) ----------
function toLogical(e) {
    const r = viewport.getBoundingClientRect();
    return { x: r1((e.clientX - r.left - panX) / scale), y: r1((e.clientY - r.top - panY) / scale) };
}

function pinchInfo() {
    const [a, b] = [...pointers.values()];
    return { dist: Math.hypot(a.x - b.x, a.y - b.y), cx: (a.x + b.x) / 2, cy: (a.y + b.y) / 2 };
}

viewport.addEventListener('pointerdown', (e) => {
    try { viewport.setPointerCapture(e.pointerId); } catch (_) {}
    pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });

    if (pointers.size === 2) {
        cancelStroke();
        isPanning = false;
        pinch = pinchInfo();
        return;
    }
    if (pointers.size > 2) return;

    if (e.button === 1 || currentMode === 'pan' || isSpacePressed) {
        isPanning = true;
        startX = e.clientX - panX;
        startY = e.clientY - panY;
        viewport.style.cursor = 'grabbing';
        e.preventDefault();
    } else if (e.button === 0) {
        startDraw(e);
    }
});

viewport.addEventListener('pointermove', (e) => {
    sendCursor(e);
    if (pointers.has(e.pointerId)) pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });

    if (pinch && pointers.size >= 2) {
        const cur = pinchInfo();
        if (pinch.dist > 0) zoomAtPoint(cur.dist / pinch.dist, cur.cx, cur.cy);
        panX += cur.cx - pinch.cx;
        panY += cur.cy - pinch.cy;
        viewChanged();
        pinch = cur;
    } else if (isPanning) {
        panX = e.clientX - startX;
        panY = e.clientY - startY;
        viewChanged();
    } else if (isDrawing) {
        const evs = e.getCoalescedEvents ? e.getCoalescedEvents() : [e];
        drawing(evs.length ? evs : [e]);
    }
});

function endPointer(e) {
    pointers.delete(e.pointerId);
    if (pointers.size < 2) pinch = null;
    if (isDrawing) stopDraw();
    if (!pointers.size) {
        isPanning = false;
        viewport.style.cursor = (currentMode === 'pan' || isSpacePressed) ? 'grab' : 'crosshair';
    }
}
viewport.addEventListener('pointerup', endPointer);
viewport.addEventListener('pointercancel', endPointer);
viewport.addEventListener('pointerleave', () => send({ type: 'cursor_off' }));

// ---------- Çizim ----------
function startDraw(e) {
    flushView();
    isDrawing = true;
    myRedo = [];                                   // yeni çizgi gelince ileri alma listesi sıfırlanır
    const c = toLogical(e);
    myStroke = { id: myRole + (++strokeCounter), owner: myRole, color: currentColor,
                 size: currentSize, mode: currentMode, pts: [c.x, c.y] };
    lastRaw = c;
    send({ type: 'start', id: myStroke.id, owner: myRole, x: c.x, y: c.y,
           color: myStroke.color, size: myStroke.size, mode: myStroke.mode });
}

function flushPoints() {
    clearTimeout(flushTimer);
    flushTimer = null;
    if (pending.length) send({ type: 'draw', pts: pending });
    pending = [];
}

function drawing(events) {
    if (!isDrawing || !myStroke) return;
    const p = myStroke.pts, n0 = p.length / 2;
    for (const ev of events) {
        const c = toLogical(ev);
        lastRaw = c;
        // Fare konumu ekran pikseline yuvarlandığı için uzaktan çizilen çizgi yakından bakınca dalgalı olur; yumuşatılır
        const lx = p[p.length - 2], ly = p[p.length - 1];
        const sx = r1(lx + (c.x - lx) * SMOOTH), sy = r1(ly + (c.y - ly) * SMOOTH);
        const dx = sx - lx, dy = sy - ly;
        if (dx * dx + dy * dy < 0.04) continue;    // çok yakın noktaları atla
        p.push(sx, sy);
        pending.push(sx, sy);
    }
    if (!flushTimer) flushTimer = setTimeout(flushPoints, 30);
    drawSegs(activeCtx, myStroke, n0, 'source-over', false);
}

function stopDraw() {
    if (!isDrawing) return;
    isDrawing = false;
    const s = myStroke;
    myStroke = null;
    if (s) {
        if (lastRaw && s.pts.length >= 4) {         // çizgi imlecin bittiği yerde bitsin
            const dx = lastRaw.x - s.pts[s.pts.length - 2], dy = lastRaw.y - s.pts[s.pts.length - 1];
            if (dx * dx + dy * dy > 0.04) { s.pts.push(lastRaw.x, lastRaw.y); pending.push(lastRaw.x, lastRaw.y); }
        }
        drawSegs(paintCtx, s, 0, commitOp(s), true);
        strokes.push(s);
    }
    clearLayer(activeCtx, activeCanvas);
    flushPoints();
    send({ type: 'stop' });
}

function cancelStroke() {
    if (!isDrawing) return;
    isDrawing = false;
    myStroke = null;
    clearLayer(activeCtx, activeCanvas);
    pending = []; clearTimeout(flushTimer); flushTimer = null;
    send({ type: 'cancel' });
}

// ---------- Geri al / ileri al: sadece KENDİ çizgilerin ----------
function undo() {
    if (isDrawing) return;
    for (let i = strokes.length - 1; i >= 0; i--) {
        if (strokes[i].owner === myRole) {
            const s = strokes.splice(i, 1)[0];
            myRedo.push(s);
            send({ type: 'undo', id: s.id });
            renderAll();
            return;
        }
    }
}

function redo() {
    if (isDrawing) return;
    const s = myRedo.pop();
    if (!s) return;
    strokes.push(s);
    drawSegs(paintCtx, s, 0, commitOp(s), true);
    send({ type: 'redo', stroke: s });
}

// ---------- Temizle (karşı tarafın onayıyla) ----------
function doClear() { strokes = []; myRedo = []; renderAll(); }

// Uygulama içi onay penceresi (tarayıcının kendi confirm kutusu yerine)
function askConfirm(title, text, okLabel = 'Onayla', cancelLabel = 'Vazgeç') {
    if (confirmResolve) { confirmResolve(false); confirmResolve = null; }
    $('confirm-title').innerText = title;
    $('confirm-text').innerText = text;
    $('confirm-ok').innerText = okLabel;
    $('confirm-cancel').innerText = cancelLabel;
    $('confirm-modal').classList.remove('hidden');
    return new Promise((resolve) => { confirmResolve = resolve; });
}

function answerConfirm(ok) {
    $('confirm-modal').classList.add('hidden');
    if (confirmResolve) { const r = confirmResolve; confirmResolve = null; r(ok); }
}

const REQ_INFO = {
    clear:    { title: 'Çizim silinsin mi?',      local: 'Tüm çizim silinecek.',                          remote: 'tüm çizimi silmek istiyor.' },
    template: { title: 'Şablon değişsin mi?',     local: 'Şablon değişince mevcut çizimler silinir.',      remote: 'şablonu değiştirmek istiyor. Mevcut çizimler silinir.' },
    rmtemplate: { title: 'Şablon kaldırılsın mı?', local: 'Çizimlerin silinmez, sadece şablon çizgileri kalkar.', remote: 'şablonu kaldırmak istiyor.' },
    size:     { title: 'Boyut değişsin mi?',      local: 'Boyut değişince mevcut çizimler silinir.',       remote: 'tuval boyutunu değiştirmek istiyor. Mevcut çizimler silinir.' }
};

// Çizimi silecek işlemler: önce bana sorulur, sonra (bağlıysa) karşı tarafa
function requestAction(kind, action, always = false) {
    if (!strokes.length && !always) { action(); return; }   // kaybedilecek çizim yoksa sormaya gerek yok      // kaybedilecek çizim yoksa sormaya gerek yok
    const info = REQ_INFO[kind];
    const connected = conn && conn.open;
    askConfirm(info.title, info.local + (connected ? ' Arkadaşına da onay isteği gönderilecek.' : ''), 'Devam')
        .then((ok) => {
            if (!ok) return;
            if (!connected) { action(); return; }
            if (pendingAction) return;
            pendingAction = action;
            send({ type: 'req', kind });
            $('status').innerText = "Arkadaşının onayı bekleniyor...";
            setTimeout(() => {
                if (pendingAction === action) { pendingAction = null; $('status').innerText = "Onay gelmedi, işlem yapılmadı."; }
            }, 30000);
        });
}

function clearCanvas() {
    requestAction('clear', () => { doClear(); send({ type: 'clear_apply' }); });
}

// ---------- Karşı tarafın verileri ----------
let dataQueue = Promise.resolve();

function setupConnection() {
    conn.on('data', (d) => {
        dataQueue = dataQueue.then(() => handleData(d)).catch(console.error);
    });
}

function handleData(d) {
    switch (d.type) {
        case 'start':
            remoteStroke = { id: d.id, owner: d.owner, color: d.color, size: d.size, mode: d.mode, pts: [d.x, d.y] };
            break;
        case 'draw':
            if (!remoteStroke) break;
            { const n0 = remoteStroke.pts.length / 2;
              for (const v of d.pts) remoteStroke.pts.push(v);
              drawSegs(remoteCtx, remoteStroke, n0, 'source-over', false); }
            break;
        case 'stop':
            if (remoteStroke) {
                drawSegs(paintCtx, remoteStroke, 0, commitOp(remoteStroke), true);
                strokes.push(remoteStroke);
            }
            clearLayer(remoteCtx, remoteCanvas);
            remoteStroke = null;
            break;
        case 'cancel':
            clearLayer(remoteCtx, remoteCanvas);
            remoteStroke = null;
            break;
        case 'undo': {
            const i = strokes.findIndex(s => s.id === d.id);
            if (i >= 0) { strokes.splice(i, 1); renderAll(); }
            break;
        }
        case 'redo':
            strokes.push(d.stroke);
            drawSegs(paintCtx, d.stroke, 0, commitOp(d.stroke), true);
            break;
        case 'req': {
            const info = REQ_INFO[d.kind];
            if (info) askConfirm(info.title, 'Arkadaşın ' + info.remote, 'Onayla', 'Reddet')
                .then((ok) => send({ type: 'req_res', ok }));
            break;
        }
        case 'req_res': {
            if (!pendingAction) break;
            const a = pendingAction;
            pendingAction = null;
            if (d.ok) { $('status').innerText = "Bağlantı sağlandı, çizebilirsiniz! 🎉"; a(); }
            else $('status').innerText = "Arkadaşın isteği reddetti.";
            break;
        }
        case 'clear_apply':
            doClear();
            break;
        case 'cursor':
            remoteCursor = { x: d.x, y: d.y, size: d.size, color: d.color, mode: d.mode };
            updateRemoteCursor();
            clearTimeout(cursorTimer);
            cursorTimer = setTimeout(() => { remoteCursor = null; updateRemoteCursor(); }, 8000);
            break;
        case 'cursor_off':
            remoteCursor = null;
            updateRemoteCursor();
            break;
        case 'remove_template':
            currentTemplate = null; templateSrc = null; templateMips = []; drawTemplate(); updateTemplateFilter();
            break;
        case 'init_size':
            currentTemplate = null;
            setCanvasSize(d.w, d.h);
            break;
        case 'template_url':
            return applyTemplate({ kind: 'url', url: d.url });
        case 'tpl_chunk': {
            const b = tplBuffers[d.id] || (tplBuffers[d.id] = { parts: [], got: 0 });
            b.parts[d.i] = d.part;
            if (++b.got === d.n) {
                delete tplBuffers[d.id];
                return applyTemplate({ kind: 'data', w: d.w, h: d.h, dataUrl: b.parts.join('') });
            }
            break;
        }
        case 'sync_state':
            strokes = d.strokes;
            renderAll();
            break;
    }
}

function setCanvasSize(w, h) {
    LW = w; LH = h;
    $('sizePicker').max = Math.max(30, Math.round(Math.max(w, h) / 25));
    strokes = []; myRedo = [];
    myStroke = null; remoteStroke = null; isDrawing = false;
    templateSrc = null; templateMips = [];
    resetZoom();
    setTimeout(resetZoom, 50);
}

function removeTemplate() {
    if (!templateSrc) return;
    requestAction('rmtemplate', () => {
        currentTemplate = null; templateSrc = null; templateMips = []; drawTemplate(); updateTemplateFilter();
        send({ type: 'remove_template' });
    }, true);                                   // çizim olmasa da karşı tarafa sorulur
}

// ---------- İndirme (şablon çözünürlüğünde) ----------
function downloadCanvas() {
    const srcW = templateSrc ? (templateSrc.naturalWidth || templateSrc.width) : 0;
    const k = Math.max(1, Math.min(4000 / Math.max(LW, LH), srcW ? srcW / LW : 2));
    const W = Math.round(LW * k), H = Math.round(LH * k);
    const mk = () => { const c = document.createElement('canvas'); c.width = W; c.height = H; return c; };

    const p = mk();
    viewOverride = { a: k, tx: 0, ty: 0 };
    strokes.forEach(s => drawSegs(p.getContext('2d'), s, 0, commitOp(s), true));
    viewOverride = null;

    const out = mk(), oc = out.getContext('2d');
    oc.fillStyle = '#ffffff';
    oc.fillRect(0, 0, W, H);
    oc.drawImage(p, 0, 0);
    if (templateSrc) { oc.globalCompositeOperation = 'multiply'; oc.drawImage(templateSrc, 0, 0, W, H); }

    const a = document.createElement('a');
    a.download = 'ortak-cizim-eserimiz.png';
    a.href = out.toDataURL('image/png');
    a.click();
}

// ---------- Şablonlar ----------
// Resmi küçültür, açık gri/kağıt rengi arka planı beyaza çeker.
// Dönen canvas tam çözünürlükte saklanır; w/h ise koordinat sistemindeki boyuttur.
function cleanAndOptimizeTemplate(img) {
    let w = img.naturalWidth || img.width;
    let h = img.naturalHeight || img.height;
    const k = Math.min(1, MAX_TEMPLATE_DIM / Math.max(w, h));
    w = Math.round(w * k); h = Math.round(h * k);

    const cv = document.createElement('canvas');
    cv.width = w; cv.height = h;
    const ctx = cv.getContext('2d');
    ctx.fillStyle = '#ffffff';
    ctx.fillRect(0, 0, w, h);
    ctx.drawImage(img, 0, 0, w, h);
    const imgData = ctx.getImageData(0, 0, w, h);
    const d = imgData.data;
    for (let i = 0; i < d.length; i += 4) {
        if (0.299 * d[i] + 0.587 * d[i + 1] + 0.114 * d[i + 2] > 235) d[i] = d[i + 1] = d[i + 2] = 255;
    }
    ctx.putImageData(imgData, 0, 0);
    const k2 = Math.min(1, LOGICAL_MAX / Math.max(w, h));
    return { canvas: cv, w: Math.round(w * k2), h: Math.round(h * k2) };
}

// Şablonu bu cihazda uygula (hem benim hem karşı taraf için aynı fonksiyon)
function applyTemplate(t) {
    return new Promise((resolve) => {
        const img = new Image();
        if (t.kind === 'data') {
            img.onload = () => {
                currentTemplate = t;
                setCanvasSize(t.w, t.h);
                templateSrc = img;
                templateMips = buildMips(templateSrc);
                renderAll();
                resolve();
            };
            img.onerror = resolve;
            img.src = t.dataUrl;
            return;
        }
        img.crossOrigin = "Anonymous";
        img.onload = () => {
            const r = cleanAndOptimizeTemplate(img);
            currentTemplate = t;
            setCanvasSize(r.w, r.h);
            templateSrc = r.canvas;
            templateMips = buildMips(templateSrc);
            renderAll();
            resolve();
        };
        img.onerror = () => { $('status').innerText = "Şablon yüklenemedi ⚠️"; resolve(); };
        img.src = t.url;
    });
}

// Şablonu karşıya gönder (URL küçük; yüklenen dosya parçalara bölünür)
function sendTemplate(t) {
    if (!conn || !conn.open || !t) return;
    if (t.kind === 'url') { conn.send({ type: 'template_url', url: t.url }); return; }
    const id = Date.now() + Math.random();
    const n = Math.ceil(t.dataUrl.length / CHUNK);
    for (let i = 0; i < n; i++) {
        conn.send({ type: 'tpl_chunk', id, i, n, w: t.w, h: t.h, part: t.dataUrl.slice(i * CHUNK, (i + 1) * CHUNK) });
    }
}

const LEVELS = [
    { id: 'kolay', name: '🟢 Kolay' },
    { id: 'orta', name: '🟡 Orta' },
    { id: 'zor', name: '🔴 Zor' }
];
let activeLevel = 'kolay';

function openTemplateModal() {
    const list = (typeof templates !== 'undefined' ? templates : [])
        .filter(t => t.url).map(t => ({ level: 'kolay', ...t }));
    if (!list.some(t => t.level === activeLevel)) {
        const first = LEVELS.find(l => list.some(t => t.level === l.id));
        if (first) activeLevel = first.id;
    }
    renderTemplates(list);
    $('template-modal').classList.remove('hidden');
}

function renderTemplates(list) {
    const tabs = $('template-tabs');
    tabs.innerHTML = '';
    LEVELS.forEach(l => {
        const n = list.filter(t => t.level === l.id).length;
        const b = document.createElement('button');
        b.className = 'px-3 py-2 rounded-xl text-xs font-bold ' +
            (l.id === activeLevel ? 'bg-pink-600 text-white' : 'bg-slate-700 text-slate-300');
        b.textContent = `📁 ${l.name} (${n})`;
        b.onclick = () => { activeLevel = l.id; renderTemplates(list); };
        tabs.appendChild(b);
    });

    const grid = $('template-grid');
    grid.innerHTML = '';
    const items = list.filter(t => t.level === activeLevel);
    if (!items.length) {
        grid.innerHTML = '<p class="col-span-2 text-center text-xs text-slate-400 py-6">Bu kategoride henüz şablon yok.</p>';
        return;
    }
    items.forEach(t => {
        const b = document.createElement('button');
        b.className = 'bg-slate-700 hover:bg-slate-600 rounded-xl p-2 flex flex-col gap-1.5 items-center';
        b.innerHTML = '<img loading="lazy" class="w-full aspect-square object-contain bg-white rounded-lg"><span class="text-xs font-bold"></span>';
        b.querySelector('img').src = t.thumb || t.url;
        b.querySelector('span').textContent = t.name;
        b.onclick = () => selectTemplate(t);
        grid.appendChild(b);
    });
}

function closeTemplateModal() { $('template-modal').classList.add('hidden'); }

function selectTemplate(t) {
    closeTemplateModal();
    const tpl = { kind: 'url', url: t.url };
    requestAction('template', () => { applyTemplate(tpl); sendTemplate(tpl); });
}

$('imageLoader').addEventListener('change', (e) => {
    const file = e.target.files[0];
    if (!file) return;
    const reader = new FileReader();
    reader.onload = (ev) => {
        const img = new Image();
        img.onload = () => {
            const r = cleanAndOptimizeTemplate(img);
            const t = { kind: 'data', w: r.w, h: r.h, dataUrl: r.canvas.toDataURL('image/png') };
            requestAction('template', () => { applyTemplate(t); sendTemplate(t); });
        };
        img.src = ev.target.result;
    };
    reader.readAsDataURL(file);
    e.target.value = '';
});

// ---------- Tuval boyutu menüsü ----------
function openSizeModal() { $('size-modal').classList.remove('hidden'); }
function closeSizeModal() { $('size-modal').classList.add('hidden'); }

function applyCustomSize() {
    const clamp = (v) => Math.min(MAX_CANVAS, Math.max(MIN_CANVAS, parseInt(v, 10) || 1000));
    const w = clamp($('custom-w').value), h = clamp($('custom-h').value);
    $('custom-w').value = w; $('custom-h').value = h;
    changeCanvasSize(w, h);
}

function changeCanvasSize(w, h) {
    closeSizeModal();
    requestAction('size', () => {
        currentTemplate = null;
        setCanvasSize(w, h);
        send({ type: 'init_size', w, h });
    });
}

// ---------- P2P bağlantı ve oda ----------
const PEER_OPTIONS = {
    config: {
        iceServers: [
            { urls: 'stun:stun.l.google.com:19302' },
            { urls: 'stun:stun1.l.google.com:19302' }
            // Mobil veriyle bağlanamama olursa buraya TURN sunucusu ekle:
            // { urls: 'turn:SUNUCU:3478', username: '...', credential: '...' }
        ]
    }
};

function generateRoomCode(length = 6) {
    const chars = 'ABCDEFGHJKMNPQRSTUVWXYZ23456789';
    let r = '';
    for (let i = 0; i < length; i++) r += chars.charAt(Math.floor(Math.random() * chars.length));
    return r;
}

function showGame() {
    $('menu-screen').classList.add('hidden');
    $('room-modal').classList.add('hidden');
    $('game-screen').classList.remove('hidden');
    setTimeout(resetZoom, 50);
}

function createRoom() {
    myRole = 'h';
    setCanvasSize(600, 600);

    peer = new Peer(generateRoomCode(6), PEER_OPTIONS);
    peer.on('open', (id) => {
        $('menu-screen').classList.add('hidden');
        $('room-modal').classList.remove('hidden');
        $('room-code-display').value = id;
    });
    peer.on('error', (err) => {
        if (err.type === 'unavailable-id') createRoom();
        else alert("Bağlantı hatası: " + err.type);
    });
    peer.on('connection', (connection) => {
        conn = connection;
        setupConnection();
        conn.on('open', () => {
            conn.send({ type: 'init_size', w: LW, h: LH });
            sendTemplate(currentTemplate);
            if (strokes.length) conn.send({ type: 'sync_state', strokes });
        });
        showGame();
        $('status').innerText = "Bağlantı sağlandı, çizebilirsiniz! 🎉";
    });
}

function roomLink() {
    return location.origin + location.pathname + '?oda=' + $('room-code-display').value;
}

function copyText(text) {
    const fallback = () => {
        const t = document.createElement('textarea');
        t.value = text;
        document.body.appendChild(t);
        t.select();
        document.execCommand('copy');
        t.remove();
    };
    if (!navigator.clipboard) { fallback(); return Promise.resolve(); }
    return navigator.clipboard.writeText(text).catch(fallback);
}

// Telefonda paylaşım menüsü açılır, bilgisayarda bağlantı doğrudan panoya kopyalanır
function shareLink() {
    const url = roomLink();
    if (navigator.share && matchMedia('(pointer: coarse)').matches) {
        navigator.share({ title: 'Birlikte Çiz', text: 'Benimle birlikte çiz! 🎨', url }).catch(() => {});
        return;
    }
    copyText(url).then(() => {
        $('copy-feedback').innerText = "Bağlantı kopyalandı, Ctrl+V ile yapıştır ✔️";
        setTimeout(() => { $('copy-feedback').innerText = ""; }, 3000);
    });
}

function copyCode() {
    const input = $('room-code-display');
    input.select();
    copyText(input.value);
    $('copy-feedback').innerText = "Kopyalandı! ✔️";
    setTimeout(() => { $('copy-feedback').innerText = ""; }, 2000);
}

function closeModalToGame() {
    showGame();
    $('status').innerText = "Arkadaşının katılması bekleniyor...";
}

function joinRoom() {
    const roomID = $('room-input').value.trim().toUpperCase();
    if (!roomID) { alert("Lütfen oda kodu gir!"); return; }
    myRole = 'g';

    peer = new Peer(PEER_OPTIONS);
    peer.on('error', (err) => {
        if (err.type === 'peer-unavailable') alert("Oda bulunamadı. Kod doğru mu ve oda hâlâ açık mı?");
        else alert("Bağlantı hatası: " + err.type);
    });
    peer.on('open', () => {
        conn = peer.connect(roomID, { reliable: true });
        setupConnection();
        conn.on('open', () => {
            showGame();
            $('status').innerText = "Bağlantı sağlandı, çizebilirsiniz! 🎉";
        });
    });
}

// Bağlantıyla gelen kişi doğrudan odaya katılır (?oda=KOD)
const urlRoom = new URLSearchParams(location.search).get('oda');
if (urlRoom) {
    $('room-input').value = urlRoom.toUpperCase();
    joinRoom();
}
