// ===================== Birlikte Boya =====================
// Çizgiler piksel değil NOKTA LİSTESİ olarak tutulur; ekran her zoom'da yeniden çizilir (keskin).
const $ = (id) => document.getElementById(id);

const viewport = $('viewport');
const container = $('canvas-container');      // beyaz kağıt (CSS ile ölçeklenir)
const paintCanvas = $('paintCanvas');         // kalıcı çizgiler
const activeCanvas = $('activeCanvas');       // benim devam eden çizgim
const remoteCanvas = $('remoteCanvas');       // karşı tarafın devam eden çizgisi
const templateCanvas = $('templateCanvas');   // şablon çizgileri
const layers = [paintCanvas, activeCanvas, remoteCanvas, templateCanvas];
const cursorEl = $('remote-cursor');          // karşı tarafın imleci (adıyla)
const myCursorEl = $('my-cursor');            // kendi fırça halkam
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
let remoteCursor = null, cursorTimer = 0, lastCursorSent = 0, lastPtr = null;
let myName = '', peerName = '';
let finished = false, swapped = false, revealed = false;   // resim bitirildi mi / bölünmüş modda taraflar değişti mi
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

const ICON_PEN = $('btn-pen').innerHTML, ICON_ERASER = $('btn-eraser').innerHTML;   // HTML'deki simgeler

// ---------- Pastel fırça (taneli doku) ----------
const GRAIN = 256;
const GRAIN_LO = 0.15, GRAIN_W = 0.20;   // yoğunluk: LO küçüldükçe daha dolgun (az beyaz), W küçüldükçe daha keskin
const GRAIN_SCALE = 0.6;                 // tane boyu: küçüldükçe daha ince
let grainAlpha = null;
const grainTiles = new Map();                           // renk -> renkli doku karosu

function mulberry32(a) {                                // sabit tohumlu rastgele: iki ekranda doku aynı olur
    return function () {
        a |= 0; a = a + 0x6D2B79F5 | 0;
        let t = Math.imul(a ^ a >>> 15, 1 | a);
        t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
        return ((t ^ t >>> 14) >>> 0) / 4294967296;
    };
}

let grainFieldCache = null;
function grainField() {                                  // 0-1 arası yumuşatılmış, sabit tohumlu gürültü
    if (grainFieldCache) return grainFieldCache;
    const rnd = mulberry32(20261126), raw = new Float32Array(GRAIN * GRAIN);
    for (let i = 0; i < raw.length; i++) raw[i] = rnd();
    const out = new Float32Array(GRAIN * GRAIN);
    for (let y = 0; y < GRAIN; y++) {
        for (let x = 0; x < GRAIN; x++) {                // 3x3 yumuşatma: taneler kümelenir
            let acc = 0;
            for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) acc += raw[((y + dy + GRAIN) % GRAIN) * GRAIN + (x + dx + GRAIN) % GRAIN];
            out[y * GRAIN + x] = acc / 9;
        }
    }
    return (grainFieldCache = out);
}

function makeGrain() {
    const f = grainField(), out = new Uint8ClampedArray(f.length);
    for (let i = 0; i < f.length; i++) out[i] = Math.max(0, Math.min(1, (f[i] - GRAIN_LO) / GRAIN_W)) * 255;
    return out;
}

// Kazımada alttaki rengin üstüne binen "kâğıt boşlukları" (beyaz tanecikler): renk pastelle boyanmış gibi görünür
const SCRATCH_LO = 0.20, SCRATCH_W = 0.22, SCRATCH_HOLE = 0.8;   // LO büyüdükçe daha çok beyaz tanecik
let scratchTile = null, scratchTileUrl = null, scratchGrain = true;
function scratchGrainTile() {
    if (scratchTile) return scratchTile;
    const f = grainField(), t = document.createElement('canvas');
    t.width = t.height = GRAIN;
    const cx = t.getContext('2d'), img = cx.createImageData(GRAIN, GRAIN);
    for (let i = 0; i < f.length; i++) {
        const cover = Math.max(0, Math.min(1, (f[i] - SCRATCH_LO) / SCRATCH_W));   // boya ne kadar tutmuş
        img.data[4 * i] = img.data[4 * i + 1] = img.data[4 * i + 2] = 255;
        img.data[4 * i + 3] = Math.round((1 - cover) * 255 * SCRATCH_HOLE);
    }
    cx.putImageData(img, 0, 0);
    return (scratchTile = t);
}
function paintScratchGrain(ctx, W, H, k) {               // indirilen resim için aynı doku (k: birim başına piksel)
    const pat = ctx.createPattern(scratchGrainTile(), 'repeat');
    pat.setTransform(new DOMMatrix().scale(GRAIN_SCALE * k));
    ctx.fillStyle = pat;
    ctx.fillRect(0, 0, W, H);
}

function grainTile(color) {
    if (!/^#[0-9a-f]{6}$/i.test(color)) color = '#000000';
    let t = grainTiles.get(color);
    if (t) return t;
    if (!grainAlpha) grainAlpha = makeGrain();
    if (grainTiles.size > 40) grainTiles.clear();
    t = document.createElement('canvas');
    t.width = t.height = GRAIN;
    const cx = t.getContext('2d'), img = cx.createImageData(GRAIN, GRAIN);
    const n = parseInt(color.slice(1), 16), r = n >> 16, g = (n >> 8) & 255, b = n & 255;
    for (let i = 0; i < grainAlpha.length; i++) {
        img.data[4 * i] = r; img.data[4 * i + 1] = g; img.data[4 * i + 2] = b; img.data[4 * i + 3] = grainAlpha[i];
    }
    cx.putImageData(img, 0, 0);
    grainTiles.set(color, t);
    return t;
}

// Pastel çizgi TEK yol olarak çizilir (parça parça çizilirse üst üste binen yerler koyulaşır)
function drawPastel(ctx, s) {
    const p = s.pts, n = p.length / 2;
    let pat;
    try {
        pat = ctx.createPattern(grainTile(s.color), 'repeat');
        pat.setTransform(new DOMMatrix().scale(GRAIN_SCALE));   // doku kâğıda bağlıdır, zoom'la birlikte büyür
    } catch (_) { pat = s.color; }
    ctx.strokeStyle = ctx.fillStyle = pat;
    ctx.beginPath();
    if (n === 1) { ctx.arc(p[0], p[1], s.size / 2, 0, Math.PI * 2); ctx.fill(); return; }
    ctx.moveTo(p[0], p[1]);
    for (let i = 1; i < n; i++) ctx.lineTo(p[2 * i], p[2 * i + 1]);
    ctx.stroke();
}

let brush = 'solid';                                    // 'solid' (düz) | 'pastel'
function setBrush(b) { brush = b; setMode('pen'); }

// ---------- Oyun modları ----------
// enabled:false olan modlar henüz hazır değil; seçim kutusunda görünmez.
const MODES = {
    together: { name: '🎨 Birlikte', info: 'Herkes tüm tuvale boyar', enabled: true },
    split:    { name: '✂️ Bölünmüş', info: 'Sen sol yarıyı, arkadaşın sağ yarıyı boyar', enabled: true },
    scratch:  { name: '✨ Kazıma', info: 'Siyahı kazı, altından renkler çıksın', enabled: true }
};
let gameMode = 'together';       // odanın modu (host seçer, katılan hello ile öğrenir)
let selectedMode = 'together';   // giriş ekranındaki seçim

function setGameMode(mode) {
    gameMode = MODES[mode] ? mode : 'together';
    document.body.dataset.mode = gameMode;
    const sc = gameMode === 'scratch';
    $('btn-pen').innerHTML = sc ? '⛏️' : ICON_PEN;
    $('btn-pen').title = sc ? 'Kazı' : 'Kalem';
    $('btn-eraser').innerHTML = sc ? '⬛' : ICON_ERASER;   // kazımada silgi, kazılan yeri tekrar siyaha boyar
    $('btn-eraser').title = sc ? 'Kapat (tekrar siyaha boya)' : 'Silgi';
    if (sc) { brush = 'solid'; setMode('pen'); }
    if (sc) { currentSize = 3; $('sizePicker').value = 3; $('sizeValue').innerText = 3; }
    applyPattern();
    layoutTopBar();                                  // düğme sayısı çubuk genişliğini değiştirir
    updateSplitOverlay();
    renderAll();
}

// Mod kancaları: yeni modlar bu iki fonksiyonu genişletir
// Bölünmüş modda oda kuran sol yarıyı, katılan sağ yarıyı boyar
function zoneBySide(side) {
    const half = LW / 2;
    return side === 'L' ? [0, 0, half, LH] : [half, 0, LW - half, LH];
}
function mySide() {                                      // şu an hangi yarı benim: 'L' sol, 'R' sağ
    return (myRole === 'h') !== swapped ? 'L' : 'R';
}
function clipRectFor(s) {                               // çizginin görünebileceği alan [x, y, genişlik, yükseklik]
    if (gameMode !== 'split') return [0, 0, LW, LH];
    return zoneBySide(s.side || (s.owner === 'h' ? 'L' : 'R'));
}
function canStartAt(x, y) {                             // çizime başlanabilecek yer mi
    if (finished) { notify('Resim tamamlandı. Devam etmek için "Devam et"e bas.'); return false; }
    if (gameMode !== 'split') return true;
    const z = zoneBySide(mySide());
    if (x >= z[0] && x < z[0] + z[2]) return true;
    notify('Bu yarı arkadaşının alanı 🙂');
    return false;
}

let notifyTimer = 0, statusBeforeNotify = null;
function notify(text) {                                 // durum çubuğunda kısa uyarı
    const el = $('status');
    if (statusBeforeNotify === null) statusBeforeNotify = el.innerText;
    el.innerText = text;
    clearTimeout(notifyTimer);
    notifyTimer = setTimeout(() => { el.innerText = statusBeforeNotify; statusBeforeNotify = null; }, 1800);
}

// Ayırıcı çizgi, soluk karşı yarı ve isim etiketleri (ekran koordinatında, zoom'la birlikte hareket eder)
function updateSplitOverlay() {
    const on = gameMode === 'split' && !finished;
    ['split-dim', 'split-line', 'split-label-h', 'split-label-g'].forEach(id => { $(id).style.display = on ? 'block' : 'none'; });
    if (!on) return;
    const half = LW / 2, h = LH * scale;
    const sx = (x) => panX + x * scale;
    const dim = $('split-dim');
    dim.style.transform = `translate(${sx(mySide() === 'L' ? half : 0)}px, ${panY}px)`;
    dim.style.width = half * scale + 'px';
    dim.style.height = h + 'px';
    const blind = !revealed;                         // bitirene kadar karşı yarı tamamen kapalı
    dim.style.display = 'flex';
    dim.style.background = blind ? '#1e293b' : 'rgba(100,116,139,.14)';
    const txt = blind ? '🙈 Arkadaşının alanı\nBitirince göreceksin' : '';
    if (dim.textContent !== txt) dim.textContent = txt;
    const line = $('split-line');
    line.style.transform = `translate(${sx(half) - 1}px, ${panY}px)`;
    line.style.height = h + 'px';
    const leftRole = swapped ? 'g' : 'h';
    [[0, leftRole], [half, leftRole === 'h' ? 'g' : 'h']].forEach(([x0, role]) => {
        const el = $('split-label-' + role);
        const mine = role === myRole;
        const name = mine ? myName : peerName;
        el.textContent = (name || (role === 'g' ? 'Bekleniyor...' : '')) + (mine ? ' (sen)' : '');
        el.style.background = mine ? '#ec4899' : '#475569';
        el.style.color = '#fff';
        el.style.display = (sx(x0 + half) > 0 && sx(x0) < cssW) ? 'block' : 'none';
        el.style.transform = `translate(${Math.max(sx(x0) + 6, 6)}px, ${Math.max(panY + 6, 6)}px)`;
    });
}

// Yer değiştir (iki tarafın onayıyla): sonraki çizgiler yeni yarıya yapılır, eskiler yerinde kalır
function swapSides() {
    requestAction('swap', () => { applySwap(!swapped); send({ type: 'swap_apply', swapped }); }, true);
}
function applySwap(v) {
    swapped = v;
    updateSplitOverlay();
    notify('Taraflar değişti: şimdi ' + (mySide() === 'L' ? 'sol' : 'sağ') + ' yarı senin');
}

// Bitirdik (iki tarafın onayıyla): çizim kilitlenir, tamamlanmış resim gösterilir
function setFinished(v) {
    finished = v;
    revealed = v;                                    // bitirilince arkadaşının yarısı açılır, devam edilince tekrar kapanır
    $('finish-bar').classList.toggle('hidden', !v);
    if (v) { cancelStroke(); closeToolbar(); }
    updateSplitOverlay();
}
function finishDrawing() {
    requestAction('finish', () => { setFinished(true); send({ type: 'finish_apply' }); }, true);
}
function resumeDrawing() {
    setFinished(false);
    send({ type: 'finish_resume' });
}

function buildModeSelect() {
    const list = Object.entries(MODES).filter(([, m]) => m.enabled);
    if (list.length < 2) return;                         // tek mod varsa seçim gösterilmez
    $('mode-select').classList.remove('hidden');
    const box = $('mode-options');
    const paint = () => {
        box.innerHTML = '';
        list.forEach(([id, m]) => {
            const b = document.createElement('button');
            b.textContent = m.name;
            b.title = m.info;
            b.className = 'flex-1 px-2 py-2 rounded-xl text-xs font-bold ' +
                (id === selectedMode ? 'bg-pink-600 text-white' : 'bg-slate-700 text-slate-300');
            b.onclick = () => { selectedMode = id; paint(); };
            box.appendChild(b);
        });
        $('mode-info').textContent = MODES[selectedMode].info;
    };
    paint();
}

// ---------- Kazıma desenleri (CSS ve canvas'ta aynı görünür) ----------
const PATTERNS = (() => {
    const smooth = (cols) => cols.map((c, i) => [i / (cols.length - 1), c]);
    const bands = (cols, n) => {
        const st = [];
        for (let i = 0; i < n; i++) { const c = cols[i % cols.length]; st.push([i / n, c], [(i + 1) / n, c]); }
        return st;
    };
    return {
        rainbow: { name: 'Gökkuşağı', angle: 135, stops: smooth(['#ff3b30', '#ff9500', '#ffd60a', '#34c759', '#00c7be', '#0a84ff', '#bf5af2']) },
        neon:    { name: 'Neon', angle: 45, stops: smooth(['#ff00cc', '#7c3aed', '#3b82f6', '#00ffd5', '#a3ff00', '#ffee00']) },
        pastel:  { name: 'Pastel', angle: 160, stops: smooth(['#ffb3c7', '#ffd6a5', '#fdffb6', '#caffbf', '#9bf6ff', '#a0c4ff', '#bdb2ff']) },
        bands:   { name: 'Şeritler', angle: 120, stops: bands(['#ef4444', '#f97316', '#facc15', '#22c55e', '#3b82f6', '#a855f7'], 24) },
        sunset:  { name: 'Gün batımı', angle: 180, stops: smooth(['#ffe259', '#ff7e5f', '#c471ed', '#12c2e9']) }
    };
})();
let patternId = 'rainbow';

const patternCss = (p) => `linear-gradient(${p.angle}deg, ${p.stops.map(([o, c]) => `${c} ${(o * 100).toFixed(3)}%`).join(', ')})`;

function paintPattern(ctx, W, H, p) {                   // CSS gradient ile aynı eğimde canvas gradient
    const a = p.angle * Math.PI / 180, dx = Math.sin(a), dy = -Math.cos(a);
    const len = Math.abs(W * dx) + Math.abs(H * dy);
    const g = ctx.createLinearGradient(W / 2 - dx * len / 2, H / 2 - dy * len / 2, W / 2 + dx * len / 2, H / 2 + dy * len / 2);
    p.stops.forEach(([o, c]) => g.addColorStop(o, c));
    ctx.fillStyle = g;
    ctx.fillRect(0, 0, W, H);
}

function applyPattern() {
    if (gameMode !== 'scratch') { container.style.background = ''; return; }
    const grad = patternCss(PATTERNS[patternId]);
    if (!scratchGrain) { container.style.background = grad; return; }
    if (!scratchTileUrl) scratchTileUrl = scratchGrainTile().toDataURL('image/png');
    const px = GRAIN * GRAIN_SCALE;                       // doku kâğıda bağlı, zoom'la birlikte büyür
    container.style.background = `url(${scratchTileUrl}) 0 0 / ${px}px ${px}px repeat, ${grad}`;
}

function updateGrainButton() {
    const b = $('btn-grain');
    if (!b) return;
    b.style.outline = scratchGrain ? '3px solid #fff' : '';
    b.style.outlineOffset = '1px';
}

function toggleGrain() {
    scratchGrain = !scratchGrain;
    applyPattern();
    updateGrainButton();
    send({ type: 'pattern', id: patternId, grain: scratchGrain });
}

function selectPattern(id, silent) {
    if (!PATTERNS[id]) return;
    patternId = id;
    applyPattern();
    $('pattern-picker').querySelectorAll('button').forEach(b => {
        if (!b.dataset.id) return;
        b.style.outline = b.dataset.id === id ? '3px solid #fff' : '';
        b.style.outlineOffset = '1px';
    });
    if (!silent) send({ type: 'pattern', id, grain: scratchGrain });
}

function buildPatternPicker() {
    Object.entries(PATTERNS).forEach(([id, p]) => {
        const b = document.createElement('button');
        b.className = 'w-9 h-9 sm:w-6 sm:h-6 rounded-full border-2 border-slate-600';
        b.style.background = patternCss(p);
        b.title = p.name;
        b.dataset.id = id;
        b.onclick = () => selectPattern(id);
        $('pattern-picker').appendChild(b);
    });
    const g = document.createElement('button');            // pastel doku aç/kapat
    g.id = 'btn-grain';
    g.textContent = '🖍️';
    g.title = 'Pastel doku (aç / kapat)';
    g.className = 'w-9 h-9 sm:w-6 sm:h-6 rounded-full border-2 border-slate-600 bg-slate-700 text-xs leading-none';
    g.onclick = toggleGrain;
    $('pattern-picker').appendChild(g);
    updateGrainButton();
    selectPattern(patternId, true);
}

// ---------- Şablon bölgeleri (dolgu aracı ve "içinde kal") ----------
const REGION_MAX = 1000, LINE_T = 180;     // bölge haritası çözünürlüğü; bu parlaklığın altı çizgi sayılır
let regionMap = null;                       // {src, w, h, line}
const fillBmp = new Map();                  // dolgu id -> hazır görüntü
const lockPath = new Map();                 // çizgi id -> bölge kırpma yolu

function ensureRegionMap() {
    if (!templateSrc || gameMode === 'scratch') return null;
    if (regionMap && regionMap.src === templateSrc) return regionMap;
    const sw = templateSrc.naturalWidth || templateSrc.width, sh = templateSrc.naturalHeight || templateSrc.height;
    const k = Math.min(1, REGION_MAX / Math.max(sw, sh));
    const w = Math.max(1, Math.round(sw * k)), h = Math.max(1, Math.round(sh * k));
    const cv = document.createElement('canvas');
    cv.width = w; cv.height = h;
    const cx = cv.getContext('2d', { willReadFrequently: true });
    cx.fillStyle = '#ffffff';
    cx.fillRect(0, 0, w, h);
    cx.drawImage(templateSrc, 0, 0, w, h);
    const d = cx.getImageData(0, 0, w, h).data;
    const line = new Uint8Array(w * h);
    for (let i = 0; i < w * h; i++) line[i] = (0.299 * d[4 * i] + 0.587 * d[4 * i + 1] + 0.114 * d[4 * i + 2]) < LINE_T ? 1 : 0;

    // Bağlı bölgeleri tek seferde etiketle (sonraki her dokunuş hazır sonucu kullanır)
    const labels = new Int32Array(w * h), stack = new Int32Array(w * h);
    const info = [null];
    let count = 0;
    for (let i0 = 0; i0 < w * h; i0++) {
        if (line[i0] || labels[i0]) continue;
        const id = ++count;
        let sp = 0, minX = w, maxX = 0, minY = h, maxY = 0;
        stack[sp++] = i0; labels[i0] = id;
        while (sp) {
            const i = stack[--sp], x = i % w, y = (i / w) | 0;
            if (x < minX) minX = x; if (x > maxX) maxX = x; if (y < minY) minY = y; if (y > maxY) maxY = y;
            let n;
            if (x > 0)     { n = i - 1; if (!line[n] && !labels[n]) { labels[n] = id; stack[sp++] = n; } }
            if (x < w - 1) { n = i + 1; if (!line[n] && !labels[n]) { labels[n] = id; stack[sp++] = n; } }
            if (y > 0)     { n = i - w; if (!line[n] && !labels[n]) { labels[n] = id; stack[sp++] = n; } }
            if (y < h - 1) { n = i + w; if (!line[n] && !labels[n]) { labels[n] = id; stack[sp++] = n; } }
        }
        info.push({ minX, maxX, minY, maxY });
    }
    regionMap = { src: templateSrc, w, h, line, labels, info, cache: new Map(), paths: new Map() };
    return regionMap;
}

// Şablon yüklendikten sonra bölge haritasını arka planda hazırla (ilk çizgide takılma olmasın)
function warmRegionMap() {
    setTimeout(() => { if (templateSrc) ensureRegionMap(); }, 250);
}

function buildRegion(R, id) {
    const { w, h, line, labels, info } = R, b = info[id], pad = 2;
    const bx = Math.max(0, b.minX - pad), by = Math.max(0, b.minY - pad);
    const bw = Math.min(w - 1, b.maxX + pad) - bx + 1, bh = Math.min(h - 1, b.maxY + pad) - by + 1;
    let mask = new Uint8Array(bw * bh);
    for (let y = 0; y < bh; y++) for (let x = 0; x < bw; x++) mask[y * bw + x] = labels[(by + y) * w + bx + x] === id ? 1 : 0;
    for (let pass = 0; pass < 2; pass++) {            // çizginin altına 2 piksel taşır: kenarda boşluk kalmaz
        const next = mask.slice();
        for (let y = 0; y < bh; y++) {
            for (let x = 0; x < bw; x++) {
                const j = y * bw + x;
                if (mask[j] || !line[(by + y) * w + bx + x]) continue;
                if ((x > 0 && mask[j - 1]) || (x < bw - 1 && mask[j + 1]) || (y > 0 && mask[j - bw]) || (y < bh - 1 && mask[j + bw])) next[j] = 1;
            }
        }
        mask = next;
    }
    return { id, w, h, bx, by, bw, bh, mask };
}

// (lx, ly) noktasının bulunduğu, çizgilerle çevrili bölgeyi bulur
function regionAt(lx, ly) {
    const R = ensureRegionMap();
    if (!R) return null;
    const { w, h, line, labels } = R;
    let sx = Math.min(w - 1, Math.max(0, Math.round(lx / LW * w)));
    let sy = Math.min(h - 1, Math.max(0, Math.round(ly / LH * h)));
    if (line[sy * w + sx]) {                          // çizgi üstüne denk geldiyse yakındaki boş pikseli ara
        let found = false;
        for (let r = 1; r <= 6 && !found; r++) {
            for (let dy = -r; dy <= r && !found; dy++) {
                for (let dx = -r; dx <= r; dx++) {
                    const x = sx + dx, y = sy + dy;
                    if (x >= 0 && y >= 0 && x < w && y < h && !line[y * w + x]) { sx = x; sy = y; found = true; break; }
                }
            }
        }
        if (!found) return null;
    }
    const id = labels[sy * w + sx];
    if (!id) return null;
    let g = R.cache.get(id);
    if (!g) { g = buildRegion(R, id); R.cache.set(id, g); }
    return g;
}

// Köşe sayısını azaltan sadeleştirme (Douglas-Peucker): kırpma yolu hafif kalsın
function simplifyLoop(pts, eps) {
    const n0 = pts.length, a = [];
    for (let i = 0; i < n0; i++) {
        const p = pts[(i + n0 - 1) % n0], c = pts[i], n = pts[(i + 1) % n0];
        if ((c[0] - p[0]) * (n[1] - c[1]) !== (c[1] - p[1]) * (n[0] - c[0])) a.push(c);
    }
    if (a.length < 4) return a;
    let far = 1, fd = 0;
    for (let i = 1; i < a.length; i++) {
        const d = (a[i][0] - a[0][0]) ** 2 + (a[i][1] - a[0][1]) ** 2;
        if (d > fd) { fd = d; far = i; }
    }
    const dp = (list) => {
        if (list.length < 3) return list;
        const x0 = list[0][0], y0 = list[0][1], x1 = list[list.length - 1][0], y1 = list[list.length - 1][1];
        const L = Math.hypot(x1 - x0, y1 - y0) || 1;
        let idx = -1, md = 0;
        for (let i = 1; i < list.length - 1; i++) {
            const d = Math.abs((x1 - x0) * (y0 - list[i][1]) - (x0 - list[i][0]) * (y1 - y0)) / L;
            if (d > md) { md = d; idx = i; }
        }
        if (md <= eps) return [list[0], list[list.length - 1]];
        return dp(list.slice(0, idx + 1)).slice(0, -1).concat(dp(list.slice(idx)));
    };
    const part1 = dp(a.slice(0, far + 1)), part2 = dp(a.slice(far).concat([a[0]]));
    return part1.slice(0, -1).concat(part2.slice(0, -1));
}

// Bölge maskesinin dış hattını çıkarır (delikler dahil), bir kez hesaplanıp saklanır
function regionPath(g) {
    const R = regionMap;
    if (R.paths.has(g.id)) return R.paths.get(g.id);
    const { bx, by, bw, bh, mask } = g, W1 = bw + 1;
    const out = new Map();
    const at = (x, y) => x >= 0 && y >= 0 && x < bw && y < bh && mask[y * bw + x] === 1;
    const add = (x0, y0, x1, y1) => {
        const k = y0 * W1 + x0, a = out.get(k);
        if (a) a.push(y1 * W1 + x1); else out.set(k, [y1 * W1 + x1]);
    };
    for (let y = 0; y < bh; y++) {
        for (let x = 0; x < bw; x++) {
            if (!mask[y * bw + x]) continue;
            if (!at(x, y - 1)) add(x, y, x + 1, y);
            if (!at(x + 1, y)) add(x + 1, y, x + 1, y + 1);
            if (!at(x, y + 1)) add(x + 1, y + 1, x, y + 1);
            if (!at(x - 1, y)) add(x, y + 1, x, y);
        }
    }
    const kx = LW / g.w, ky = LH / g.h, path = new Path2D();
    for (const [start, list] of out) {
        while (list.length) {
            const loop = [];
            let k = start;
            do {
                loop.push(k);
                const a = out.get(k);
                if (!a || !a.length) break;
                k = a.pop();
            } while (k !== start);
            if (loop.length < 3) continue;
            const simp = simplifyLoop(loop.map(v => [v % W1, (v / W1) | 0]), 1.0);
            simp.forEach(([x, y], i) => {
                const X = (bx + x) * kx, Y = (by + y) * ky;
                if (i) path.lineTo(X, Y); else path.moveTo(X, Y);
            });
            path.closePath();
        }
    }
    R.paths.set(g.id, path);
    return path;
}

function fillBitmap(f) {
    if (fillBmp.has(f.id)) return fillBmp.get(f.id);
    const g = regionAt(f.x, f.y);
    let b = null;
    if (g) {
        const cv = document.createElement('canvas');
        cv.width = g.bw; cv.height = g.bh;
        const cx = cv.getContext('2d'), img = cx.createImageData(g.bw, g.bh);
        const n = parseInt(f.color.slice(1), 16), r = n >> 16, gr = (n >> 8) & 255, bl = n & 255;
        for (let i = 0; i < g.mask.length; i++) {
            if (g.mask[i]) { const o = 4 * i; img.data[o] = r; img.data[o + 1] = gr; img.data[o + 2] = bl; img.data[o + 3] = 255; }
        }
        cx.putImageData(img, 0, 0);
        b = { cv, g };
    }
    fillBmp.set(f.id, b);
    return b;
}

function drawFill(ctx, f) {
    const b = fillBitmap(f);
    if (!b) return;
    const g = b.g, kx = LW / g.w, ky = LH / g.h;
    ctx.save();
    applyView(ctx);
    const cr = clipRectFor(f);
    ctx.beginPath(); ctx.rect(cr[0], cr[1], cr[2], cr[3]); ctx.clip();
    ctx.imageSmoothingEnabled = true;
    ctx.drawImage(b.cv, g.bx * kx, g.by * ky, g.bw * kx, g.bh * ky);
    ctx.restore();
}

function drawItem(ctx, s) {
    if (s.kind === 'fill') drawFill(ctx, s);
    else drawSegs(ctx, s, 0, commitOp(s), true);
}

// "İçinde kal" açıkken çizgi, başladığı bölgenin dışına taşmaz
function lockClip(s) {
    if (!s.lock) return null;
    if (lockPath.has(s.id)) return lockPath.get(s.id);
    const g = regionAt(s.pts[0], s.pts[1]);
    const p = g ? regionPath(g) : null;
    lockPath.set(s.id, p);
    return p;
}

function doFill(e) {
    const c = toLogical(e);
    if (!canStartAt(c.x, c.y)) return;
    if (!templateSrc || gameMode === 'scratch') { notify('Dolgu için önce bir şablon seç'); return; }
    const f = { id: myRole + (++strokeCounter), owner: myRole, side: mySide(), kind: 'fill', color: currentColor, x: c.x, y: c.y };
    if (!fillBitmap(f)) { notify('Buraya dolgu yapılamadı'); return; }
    myRedo = [];
    strokes.push(f);
    drawFill(paintCtx, f);
    send({ type: 'fill', item: f });
}

// Damlalık: resimdeki bir rengi seçer (özel renkleri tekrar bulmak için)
function pickColor(e) {
    flushView();
    const r = viewport.getBoundingClientRect();
    const x = Math.floor((e.clientX - r.left) * dpr), y = Math.floor((e.clientY - r.top) * dpr);
    if (x < 0 || y < 0 || x >= paintCanvas.width || y >= paintCanvas.height) return;
    if (gameMode === 'split' && !revealed) {         // arkadaşının alanından renk alınamaz
        const z = zoneBySide(mySide() === 'L' ? 'R' : 'L');
        const lx = (e.clientX - r.left - panX) / scale;
        if (lx >= z[0] && lx < z[0] + z[2]) { notify('Arkadaşının alanı bitince görünecek'); return; }
    }
    const d = paintCtx.getImageData(x, y, 1, 1).data;
    if (d[3] < 128) { notify('Burada boya yok'); return; }
    const wasPick = currentMode === 'pick';
    setColor('#' + [d[0], d[1], d[2]].map(v => v.toString(16).padStart(2, '0')).join(''));
    if (wasPick) setMode('pen');                    // renk alınca kaleme dön
}

// ---------- İsim ----------
function loadName() {
    try { myName = localStorage.getItem('bc-name') || ''; } catch (_) {}
    $('name-input').value = myName;
}

function readName() {
    myName = ($('name-input').value || '').trim().slice(0, 16) || 'Misafir';
    $('name-input').value = myName;
    try { localStorage.setItem('bc-name', myName); } catch (_) {}
    return myName;
}

const connectedStatus = () => peerName
    ? `${peerName} ile bağlandın, çizebilirsiniz! 🎉`
    : "Bağlantı sağlandı, çizebilirsiniz! 🎉";

// ---------- Araçlar ----------
$('sizePicker').addEventListener('input', (e) => {
    currentSize = Number(e.target.value);
    $('sizeValue').innerText = currentSize;
    updateMyCursor();
});

function setMode(mode) {
    currentMode = mode;
    const base = "inline-flex items-center justify-center text-[18px] leading-5 px-3 py-2 sm:py-1 rounded-lg font-bold transition ";
    const on = "bg-pink-600 text-white", off = "text-slate-400 hover:text-white";
    $('btn-pen').className = base + (mode === 'pen' && brush === 'solid' ? on : off);
    $('btn-pastel').className = 'no-scratch ' + base + (mode === 'pen' && brush === 'pastel' ? on : off);
    $('btn-eraser').className = base + (mode === 'eraser' ? on : off);
    $('btn-pan').className = base + (mode === 'pan' ? on : off);
    $('btn-fill').className = 'no-scratch ' + base + (mode === 'fill' ? on : off);
    $('btn-pick').className = 'no-scratch ' + base + (mode === 'pick' ? on : off);
    viewport.style.cursor = mode === 'pan' ? 'grab' : 'crosshair';
    updateMyCursor();
}

const PALETTE = ['#000000', '#ef4444', '#f97316', '#facc15', '#22c55e', '#14b8a6',
                 '#3b82f6', '#6366f1', '#a855f7', '#ec4899', '#92400e', '#9ca3af'];

function setColor(c) {
    currentColor = c;
    $('colorPicker').value = c;
    if (currentMode === 'eraser' || currentMode === 'pan') setMode('pen');
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

function commitOp(s) {
    if (gameMode === 'scratch') return s.mode === 'eraser' ? 'source-over' : 'destination-out';
    return s.mode === 'eraser' ? 'destination-out' : 'source-over';
}

// Çizginin from. noktasından sonrasını parça parça çizer.
// Önizleme ve kalıcı çizim aynı yöntemi kullandığı için sonuç birebir aynıdır.
function drawSegs(ctx, s, from, op, dot) {
    const p = s.pts, n = p.length / 2;
    if (n < 2 && !(dot && n === 1)) return;
    const erase = s.mode === 'eraser';
    ctx.save();
    applyView(ctx);
    const cr = clipRectFor(s);
    ctx.beginPath(); ctx.rect(cr[0], cr[1], cr[2], cr[3]); ctx.clip();   // izin verilen alanın dışına taşma
    const lp = lockClip(s);
    if (lp) ctx.clip(lp, 'evenodd');                                                  // "içinde kal": bölgenin dışına taşma
    ctx.lineCap = ctx.lineJoin = 'round';
    ctx.lineWidth = s.size;
    ctx.globalCompositeOperation = op;
    ctx.strokeStyle = ctx.fillStyle = gameMode === 'scratch' ? '#000000' : ((erase && op === 'source-over') ? '#ffffff' : s.color);
    if (s.brush === 'pastel' && !erase && gameMode !== 'scratch') { drawPastel(ctx, s); ctx.restore(); return; }
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
    if (!templateSrc || gameMode === 'scratch') return;      // kazıma modunda şablon kullanılmaz
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
    const scratch = gameMode === 'scratch';
    if (scratch) {                                           // kazımada tuval siyahla kaplı başlar
        paintCtx.save();
        applyView(paintCtx);
        paintCtx.fillStyle = '#000000';
        paintCtx.fillRect(0, 0, LW, LH);
        paintCtx.restore();
    }
    strokes.forEach(s => drawItem(paintCtx, s));
    drawTemplate();
    updateTemplateFilter();
    clearLayer(activeCtx, activeCanvas);
    clearLayer(remoteCtx, remoteCanvas);
    if (scratch) {                                           // devam eden çizgiler doğrudan tuvale işlenir
        if (myStroke) drawSegs(paintCtx, myStroke, 0, commitOp(myStroke), false);
        if (remoteStroke) drawSegs(paintCtx, remoteStroke, 0, commitOp(remoteStroke), false);
    } else {
        if (myStroke) drawSegs(activeCtx, myStroke, 0, 'source-over', false);
        if (remoteStroke) drawSegs(remoteCtx, remoteStroke, 0, 'source-over', false);
    }
    layers.forEach(cv => { cv.style.transform = ''; });
    renderedView = { scale, panX, panY };
    lastRenderMs = performance.now() - t0;
}

function updateRemoteCursor() {
    const c = remoteCursor;
    if (!c || (gameMode === 'split' && !revealed)) { cursorEl.style.display = 'none'; return; }
    const d = c.mode === 'pan' ? 10 : Math.max(8, c.size * scale);   // halka fırça boyutunda
    cursorEl.style.display = 'block';
    cursorEl.style.width = cursorEl.style.height = d + 'px';
    cursorEl.style.transform = `translate(${panX + c.x * scale - d / 2}px, ${panY + c.y * scale - d / 2}px)`;
    cursorEl.style.borderColor = c.mode === 'eraser' ? '#334155' : c.color;
    cursorEl.style.borderStyle = c.mode === 'eraser' ? 'dashed' : 'solid';
    cursorEl.style.background = c.mode === 'pan' ? c.color : 'transparent';
    const nameEl = $('remote-cursor-name');
    const col = c.mode === 'eraser' ? '#334155' : c.color;
    nameEl.textContent = peerName;               // textContent: karşıdan gelen isim güvenle gösterilir
    nameEl.style.display = peerName ? 'block' : 'none';
    nameEl.style.background = col;
    nameEl.style.color = textOn(col);
}

function textOn(hex) {
    if (!/^#[0-9a-f]{6}$/i.test(hex)) return '#fff';
    const n = parseInt(hex.slice(1), 16);
    return (0.299 * (n >> 16) + 0.587 * ((n >> 8) & 255) + 0.114 * (n & 255)) > 150 ? '#000' : '#fff';
}

// Kendi imlecim: fırça boyutunu gösteren halka (sadece fare/kalem; yerel olduğu için ağ gecikmesi yok)
function updateMyCursor(e) {
    if (e) lastPtr = e.pointerType === 'touch' ? null : { x: e.clientX, y: e.clientY };
    if (!lastPtr || currentMode === 'pan' || currentMode === 'fill' || currentMode === 'pick') { myCursorEl.style.display = 'none'; return; }
    const r = viewport.getBoundingClientRect();
    const d = Math.max(4, currentSize * scale);
    myCursorEl.style.display = 'block';
    myCursorEl.style.width = myCursorEl.style.height = d + 'px';
    myCursorEl.style.transform = `translate(${lastPtr.x - r.left - d / 2}px, ${lastPtr.y - r.top - d / 2}px)`;
    myCursorEl.style.borderStyle = currentMode === 'eraser' ? 'dashed' : 'solid';
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
    updateMyCursor();
    updateSplitOverlay();
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
const STATUS_MIN = 300;   // durum yazısına ayrılan en az genişlik (px)
function layoutTopBar() {
    const bar = $('top-bar');
    bar.classList.remove('compact');                 // önce tam hâlini dene, genişliğini ölç
    const need = $('desktop-bar').offsetWidth + STATUS_MIN + 40;
    bar.classList.toggle('compact', bar.clientWidth < need);   // sığmıyorsa menüye geç
}
window.addEventListener('load', layoutTopBar);
if (document.fonts) document.fonts.ready.then(layoutTopBar);

const refit = () => { clearTimeout(resizeTimer); resizeTimer = setTimeout(() => { layoutTopBar(); resetZoom(); }, 150); };
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
        if (currentMode === 'pick' || e.altKey) pickColor(e);      // Alt + tıklama da renk alır
        else if (currentMode === 'fill') doFill(e);
        else startDraw(e);
    }
});

viewport.addEventListener('pointermove', (e) => {
    updateMyCursor(e);
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
viewport.addEventListener('pointerleave', () => { lastPtr = null; updateMyCursor(); send({ type: 'cursor_off' }); });

// ---------- Çizim ----------
function startDraw(e) {
    const c0 = toLogical(e);
    if (!canStartAt(c0.x, c0.y)) return;
    flushView();
    isDrawing = true;
    myRedo = [];                                   // yeni çizgi gelince ileri alma listesi sıfırlanır
    const c = toLogical(e);
    // çizgi kilidi: şablon varken her zaman açık
    myStroke = { id: myRole + (++strokeCounter), owner: myRole, side: mySide(), lock: currentMode === 'pen' && gameMode !== 'scratch' && !!templateSrc, brush: (currentMode === 'pen' && gameMode !== 'scratch') ? brush : 'solid', color: currentColor,
                 size: currentSize, mode: currentMode, pts: [c.x, c.y] };
    lastRaw = c;
    send({ type: 'start', id: myStroke.id, owner: myRole, side: myStroke.side, lock: myStroke.lock, brush: myStroke.brush, x: c.x, y: c.y,
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
    if (gameMode === 'scratch') drawSegs(paintCtx, myStroke, n0, commitOp(myStroke), false);
    else if (myStroke.brush === 'pastel') { clearLayer(activeCtx, activeCanvas); drawSegs(activeCtx, myStroke, 0, 'source-over', false); }
    else drawSegs(activeCtx, myStroke, n0, 'source-over', false);
}

function stopDraw() {
    if (!isDrawing) return;
    isDrawing = false;
    const s = myStroke;
    myStroke = null;
    if (s) {
        const n0 = s.pts.length / 2;
        if (lastRaw && s.pts.length >= 4) {         // çizgi imlecin bittiği yerde bitsin
            const dx = lastRaw.x - s.pts[s.pts.length - 2], dy = lastRaw.y - s.pts[s.pts.length - 1];
            if (dx * dx + dy * dy > 0.04) { s.pts.push(lastRaw.x, lastRaw.y); pending.push(lastRaw.x, lastRaw.y); }
        }
        if (gameMode !== 'scratch') drawSegs(paintCtx, s, 0, commitOp(s), true);
        else if (n0 === 1) drawSegs(paintCtx, s, 0, commitOp(s), true);                             // tek dokunuş: nokta
        else if (s.pts.length / 2 > n0) drawSegs(paintCtx, s, n0, commitOp(s), false);              // son parça
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
    if (isDrawing || finished) return;
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
    if (isDrawing || finished) return;
    const s = myRedo.pop();
    if (!s) return;
    strokes.push(s);
    drawItem(paintCtx, s);
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
    swap:     { title: 'Yer değişsin mi?', local: 'Taraflar değişir; şu ana kadarki çizimler yerinde kalır.', remote: 'tarafları değiştirmek istiyor. Şu ana kadarki çizimler yerinde kalır.' },
    finish:   { title: 'Bitirdiğinize emin misiniz?', local: 'Çizim kilitlenir ve tamamlanmış resim gösterilir. İstediğin zaman devam edebilirsin.', remote: 'resmi bitirmek istiyor. Çizim kilitlenir, istediğiniz zaman devam edebilirsiniz.' },
    rmtemplate: { title: 'Şablon kaldırılsın mı?', local: 'Çizimlerin silinmez, sadece şablon çizgileri kalkar.', remote: 'şablonu kaldırmak istiyor.' },
    size:     { title: 'Boyut değişsin mi?',      local: 'Boyut değişince mevcut çizimler silinir.',       remote: 'tuval boyutunu değiştirmek istiyor. Mevcut çizimler silinir.' }
};

// Çizimi silecek işlemler: önce bana sorulur, sonra (bağlıysa) karşı tarafa
function requestAction(kind, action, always = false) {
    if (!strokes.length && !always) { action(); return; }   // kaybedilecek çizim yoksa sormaya gerek yok      // kaybedilecek çizim yoksa sormaya gerek yok
    const info = REQ_INFO[kind];
    const connected = conn && conn.open;
    askConfirm(info.title, info.local + (kind === 'finish' && gameMode === 'split' ? ' Arkadaşının yarısı da açılır.' : '') + (connected ? ' Arkadaşına da onay isteği gönderilecek.' : ''), 'Devam')
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
            remoteStroke = { id: d.id, owner: d.owner, side: d.side, lock: d.lock, brush: d.brush, color: d.color, size: d.size, mode: d.mode, pts: [d.x, d.y] };
            break;
        case 'draw':
            if (!remoteStroke) break;
            { const n0 = remoteStroke.pts.length / 2;
              for (const v of d.pts) remoteStroke.pts.push(v);
              if (gameMode === 'scratch') drawSegs(paintCtx, remoteStroke, n0, commitOp(remoteStroke), false);
              else if (remoteStroke.brush === 'pastel') { clearLayer(remoteCtx, remoteCanvas); drawSegs(remoteCtx, remoteStroke, 0, 'source-over', false); }
              else drawSegs(remoteCtx, remoteStroke, n0, 'source-over', false); }
            break;
        case 'stop':
            if (remoteStroke) {
                if (gameMode !== 'scratch' || remoteStroke.pts.length === 2) drawSegs(paintCtx, remoteStroke, 0, commitOp(remoteStroke), true);
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
            drawItem(paintCtx, d.stroke);
            break;
        case 'req': {
            const info = REQ_INFO[d.kind];
            if (info) askConfirm(info.title, (peerName || 'Arkadaşın') + ' ' + info.remote + (d.kind === 'finish' && gameMode === 'split' ? ' Arkadaşının yarısı da açılır.' : ''), 'Onayla', 'Reddet')
                .then((ok) => send({ type: 'req_res', ok }));
            break;
        }
        case 'req_res': {
            if (!pendingAction) break;
            const a = pendingAction;
            pendingAction = null;
            if (d.ok) { $('status').innerText = connectedStatus(); a(); }
            else $('status').innerText = (peerName || 'Arkadaşın') + " isteği reddetti.";
            break;
        }
        case 'clear_apply':
            doClear();
            break;
        case 'swap_apply':
            applySwap(!!d.swapped);
            break;
        case 'finish_apply':
            setFinished(true);
            break;
        case 'finish_resume':
            setFinished(false);
            break;
        case 'fill':
            strokes.push(d.item);
            drawFill(paintCtx, d.item);
            break;
        case 'pattern':
            if (typeof d.grain === 'boolean') { scratchGrain = d.grain; updateGrainButton(); }
            selectPattern(d.id, true);
            break;
        case 'hello':
            peerName = String(d.name || 'Misafir').slice(0, 16);
            if (d.mode) setGameMode(d.mode);
            if (typeof d.grain === 'boolean') { scratchGrain = d.grain; updateGrainButton(); }
            if (d.pattern) selectPattern(d.pattern, true);
            if (typeof d.swapped === 'boolean') swapped = d.swapped;
            updateSplitOverlay();
            $('status').innerText = connectedStatus();
            updateRemoteCursor();
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
    if (finished) setFinished(false);
    revealed = false;
    $('sizePicker').max = Math.max(30, Math.round(Math.max(w, h) / 25));
    strokes = []; myRedo = [];
    myStroke = null; remoteStroke = null; isDrawing = false;
    templateSrc = null; templateMips = [];
    regionMap = null; fillBmp.clear(); lockPath.clear();
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
    if (gameMode === 'split' && !revealed) { notify('Bölünmüş modda resmi bitirince indirebilirsin'); return; }
    const srcW = templateSrc ? (templateSrc.naturalWidth || templateSrc.width) : 0;
    const k = Math.max(1, Math.min(4000 / Math.max(LW, LH), srcW ? srcW / LW : 2));
    const W = Math.round(LW * k), H = Math.round(LH * k);
    const mk = () => { const c = document.createElement('canvas'); c.width = W; c.height = H; return c; };

    const scratch = gameMode === 'scratch';
    const p = mk();
    if (scratch) { const pc = p.getContext('2d'); pc.fillStyle = '#000000'; pc.fillRect(0, 0, W, H); }
    viewOverride = { a: k, tx: 0, ty: 0 };
    strokes.forEach(s => drawItem(p.getContext('2d'), s));
    viewOverride = null;

    const out = mk(), oc = out.getContext('2d');
    if (scratch) { paintPattern(oc, W, H, PATTERNS[patternId]); if (scratchGrain) paintScratchGrain(oc, W, H, k); }
    else { oc.fillStyle = '#ffffff'; oc.fillRect(0, 0, W, H); }
    oc.drawImage(p, 0, 0);
    if (templateSrc && !scratch) { oc.globalCompositeOperation = 'multiply'; oc.drawImage(templateSrc, 0, 0, W, H); }

    const a = document.createElement('a');
    const now = new Date(), z = (n) => String(n).padStart(2, '0');
    const stamp = `${now.getFullYear()}-${z(now.getMonth() + 1)}-${z(now.getDate())}_${z(now.getHours())}-${z(now.getMinutes())}`;
    a.download = `${scratch ? 'pastel-kazima' : 'birlikte-boya'}-${stamp}.png`;   // kazıma modunda ayrı ad + tarih/saat
    a.href = out.toDataURL('image/png');
    a.click();
}

// ---------- Resmi boyama sayfasına çevirme ----------
function boxBlur(src, w, h, r) {                        // kutu bulanıklığı (iki geçişte gauss'a yakın)
    if (r < 1) return src;
    const tmp = new Float32Array(w * h), out = new Float32Array(w * h), d = 2 * r + 1;
    for (let y = 0; y < h; y++) {
        const row = y * w;
        let acc = 0;
        for (let x = -r; x <= r; x++) acc += src[row + Math.min(w - 1, Math.max(0, x))];
        for (let x = 0; x < w; x++) {
            tmp[row + x] = acc / d;
            acc += src[row + Math.min(w - 1, x + r + 1)] - src[row + Math.max(0, x - r)];
        }
    }
    for (let x = 0; x < w; x++) {
        let acc = 0;
        for (let y = -r; y <= r; y++) acc += tmp[Math.min(h - 1, Math.max(0, y)) * w + x];
        for (let y = 0; y < h; y++) {
            out[y * w + x] = acc / d;
            acc += tmp[Math.min(h - 1, y + r + 1) * w + x] - tmp[Math.max(0, y - r) * w + x];
        }
    }
    return out;
}

function maxFilter(src, w, h, r) {                      // çizgiyi kalınlaştırır
    const tmp = new Float32Array(w * h), out = new Float32Array(w * h);
    for (let y = 0; y < h; y++) {
        const row = y * w;
        for (let x = 0; x < w; x++) {
            let m = 0;
            for (let i = Math.max(0, x - r), e = Math.min(w - 1, x + r); i <= e; i++) if (src[row + i] > m) m = src[row + i];
            tmp[row + x] = m;
        }
    }
    for (let x = 0; x < w; x++) {
        for (let y = 0; y < h; y++) {
            let m = 0;
            for (let j = Math.max(0, y - r), e = Math.min(h - 1, y + r); j <= e; j++) if (tmp[j * w + x] > m) m = tmp[j * w + x];
            out[y * w + x] = m;
        }
    }
    return out;
}

// d: RGBA verisi. method 'black': level = siyah eşiği (0-255). method 'edges': level = hassasiyet (0-100).
// Dönen: gri tonlu RGBA (beyaz zemin, siyah çizgi)
function toLineArt(d, w, h, method, level, thick) {
    const n = w * h, k = Math.max(w, h) / 1000;
    let a = new Float32Array(n);
    if (method === 'black') {
        for (let i = 0; i < n; i++) {
            const al = d[4 * i + 3] / 255;
            const m = Math.max(d[4 * i], d[4 * i + 1], d[4 * i + 2]) * al + 255 * (1 - al);   // saydam = beyaz
            a[i] = Math.min(1, Math.max(0, (level + 15 - m) / 30));                              // siyah: çizgi, diğer renkler: beyaz
        }
    } else {
        const gray = new Float32Array(n);
        for (let i = 0; i < n; i++) {
            const al = d[4 * i + 3] / 255;
            gray[i] = (0.299 * d[4 * i] + 0.587 * d[4 * i + 1] + 0.114 * d[4 * i + 2]) * al + 255 * (1 - al);
        }
        const rb = Math.max(1, Math.round(1.5 * k));
        const g = boxBlur(boxBlur(gray, w, h, rb), w, h, rb);
        const T = 30 * (1 - level / 100) + 4, soft = T * 0.6 + 3;
        for (let y = 1; y < h - 1; y++) {
            for (let x = 1; x < w - 1; x++) {
                const i = y * w + x;
                const gx = (g[i - w + 1] + 2 * g[i + 1] + g[i + w + 1]) - (g[i - w - 1] + 2 * g[i - 1] + g[i + w - 1]);
                const gy = (g[i + w - 1] + 2 * g[i + w] + g[i + w + 1]) - (g[i - w - 1] + 2 * g[i - w] + g[i - w + 1]);
                a[i] = Math.min(1, Math.max(0, (Math.hypot(gx, gy) / 4 - T) / soft));
            }
        }
    }
    const r = Math.min(6, Math.round(thick * k));
    if (r > 0) a = maxFilter(a, w, h, r);
    const out = new Uint8ClampedArray(n * 4);
    for (let i = 0; i < n; i++) {
        const v = 255 - 255 * a[i];
        out[4 * i] = out[4 * i + 1] = out[4 * i + 2] = v;
        out[4 * i + 3] = 255;
    }
    return out;
}

function convertImage(img, method, level, thick, maxSide) {
    const sw = img.naturalWidth || img.width, sh = img.naturalHeight || img.height;
    const k = Math.min(1, maxSide / Math.max(sw, sh));
    const w = Math.max(1, Math.round(sw * k)), h = Math.max(1, Math.round(sh * k));
    const cv = document.createElement('canvas');
    cv.width = w; cv.height = h;
    const cx = cv.getContext('2d', { willReadFrequently: true });
    cx.drawImage(img, 0, 0, w, h);
    const id = cx.getImageData(0, 0, w, h);
    cx.putImageData(new ImageData(toLineArt(id.data, w, h, method, level, thick), w, h), 0, 0);
    return cv;
}

const conv = { src: null, method: 'black', level: { black: 80, edges: 50 }, thick: { black: 0, edges: 1 }, timer: 0 };
const CONV_HINT = {
    black: 'Siyah çizgiler kalır, siyah dışındaki her renk beyaz olur. Dış çizgisi siyah olan resimler için.',
    edges: 'Renk geçişlerinden çizgi çıkarır. Fotoğraflar ve siyah çizgisi olmayan renkli resimler için.',
    keep: 'Resim değiştirilmeden kullanılır. Zaten boyama sayfası olan resimler için.'
};

function openConvert(img) {
    conv.src = img;
    const c = document.createElement('canvas');          // siyah çizgi var mı? ona göre başlangıç yöntemi seç
    c.width = c.height = 100;
    const cx = c.getContext('2d', { willReadFrequently: true });
    cx.fillStyle = '#fff'; cx.fillRect(0, 0, 100, 100);
    cx.drawImage(img, 0, 0, 100, 100);
    const d = cx.getImageData(0, 0, 100, 100).data;
    let dark = 0;
    for (let i = 0; i < d.length; i += 4) if (Math.max(d[i], d[i + 1], d[i + 2]) < 70) dark++;
    $('convert-modal').classList.remove('hidden');
    setConvMethod(dark / 10000 >= 0.01 ? 'black' : 'edges');
}

function setConvMethod(m) {
    conv.method = m;
    ['black', 'edges', 'keep'].forEach(id => {
        $('cv-m-' + id).className = 'flex-1 px-2 py-2 rounded-xl text-xs font-bold ' + (id === m ? 'bg-pink-600 text-white' : 'bg-slate-700 text-slate-300');
    });
    $('cv-hint').textContent = CONV_HINT[m];
    $('cv-sliders').style.display = m === 'keep' ? 'none' : 'flex';
    if (m !== 'keep') {
        const lv = $('cv-level');
        $('cv-level-label').textContent = m === 'black' ? 'Siyah eşiği' : 'Hassasiyet';
        lv.min = m === 'black' ? 10 : 0;
        lv.max = m === 'black' ? 200 : 100;
        lv.value = conv.level[m];
        $('cv-thick').value = conv.thick[m];
    }
    renderConvertPreview();
}

function onConvInput() {
    if (conv.method === 'keep') return;
    conv.level[conv.method] = Number($('cv-level').value);
    conv.thick[conv.method] = Number($('cv-thick').value);
    clearTimeout(conv.timer);
    conv.timer = setTimeout(renderConvertPreview, 30);
}

function renderConvertPreview() {
    if (!conv.src) return;
    const cv = $('convert-preview');
    const out = conv.method === 'keep'
        ? convertImageKeep(conv.src, 480)
        : convertImage(conv.src, conv.method, conv.level[conv.method], conv.thick[conv.method], 480);
    cv.width = out.width; cv.height = out.height;
    cv.getContext('2d').drawImage(out, 0, 0);
}

function convertImageKeep(img, maxSide) {               // "olduğu gibi": sadece küçültüp beyaz zemine oturtur
    const sw = img.naturalWidth || img.width, sh = img.naturalHeight || img.height;
    const k = Math.min(1, maxSide / Math.max(sw, sh));
    const cv = document.createElement('canvas');
    cv.width = Math.max(1, Math.round(sw * k)); cv.height = Math.max(1, Math.round(sh * k));
    const cx = cv.getContext('2d');
    cx.fillStyle = '#fff'; cx.fillRect(0, 0, cv.width, cv.height);
    cx.drawImage(img, 0, 0, cv.width, cv.height);
    return cv;
}

function closeConvert() { $('convert-modal').classList.add('hidden'); }

function applyConvert() {
    const img = conv.src, method = conv.method;
    const level = conv.level[method], thick = conv.thick[method];
    closeConvert();
    notify('Resim işleniyor...');
    setTimeout(() => {                                  // ekran önce güncellensin, sonra ağır işlem
        const src = method === 'keep' ? img : convertImage(img, method, level, thick, Math.min(MAX_TEMPLATE_DIM, 3000));
        const r = cleanAndOptimizeTemplate(src);
        const t = { kind: 'data', w: r.w, h: r.h, dataUrl: r.canvas.toDataURL('image/png') };
        conv.src = null;
        requestAction('template', () => { applyTemplate(t); sendTemplate(t); });
    }, 30);
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
                warmRegionMap();
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
            warmRegionMap();
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
            openConvert(img);                          // önce boyama sayfasına çevirme penceresi açılır
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
    setTimeout(() => { layoutTopBar(); resetZoom(); }, 50);
}

function createRoom() {
    myRole = 'h';
    readName();
    setGameMode(selectedMode);
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
            conn.send({ type: 'hello', name: myName, mode: gameMode, swapped, pattern: patternId, grain: scratchGrain });
            conn.send({ type: 'init_size', w: LW, h: LH });
            sendTemplate(currentTemplate);
            if (strokes.length) conn.send({ type: 'sync_state', strokes });
        });
        showGame();
        $('status').innerText = connectedStatus();
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
        navigator.share({ title: 'Birlikte Boya', text: 'Benimle birlikte boya! 🎨', url }).catch(() => {});
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
    readName();

    peer = new Peer(PEER_OPTIONS);
    peer.on('error', (err) => {
        if (err.type === 'peer-unavailable') alert("Oda bulunamadı. Kod doğru mu ve oda hâlâ açık mı?");
        else alert("Bağlantı hatası: " + err.type);
    });
    peer.on('open', () => {
        conn = peer.connect(roomID, { reliable: true });
        setupConnection();
        conn.on('open', () => {
            conn.send({ type: 'hello', name: myName });
            showGame();
            $('status').innerText = connectedStatus();
        });
    });
}

// Bağlantıyla gelen kişi doğrudan odaya katılır (?oda=KOD)
const urlRoom = new URLSearchParams(location.search).get('oda');
buildModeSelect();
buildPatternPicker();
loadName();
if (urlRoom) {
    $('room-input').value = urlRoom.toUpperCase();
    if (myName) joinRoom();
    else { $('link-hint').classList.remove('hidden'); $('name-input').focus(); }
}
