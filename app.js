'use strict';
const $ = s => document.querySelector(s);
const WHITE = 0xFFFFFFFF;
const pack = h => ((255 << 24) | (parseInt(h.slice(5, 7), 16) << 16) | (parseInt(h.slice(3, 5), 16) << 8) | parseInt(h.slice(1, 3), 16)) >>> 0;

/* ===== Framebuffer: the only place pixels are written ===== */
class Raster {
  constructor(cv, W, H) {
    this.cv = cv; this.W = W; this.H = H; cv.width = W; cv.height = H;
    this.ctx = cv.getContext('2d');
    this.img = this.ctx.createImageData(W, H);
    this.buf = new Uint32Array(this.img.data.buffer);
    this.clear();
  }
  clear() { this.buf.fill(WHITE); }
  set(x, y, c) { if (x >= 0 && x < this.W && y >= 0 && y < this.H) this.buf[y * this.W + x] = c; }
  show() { this.ctx.putImageData(this.img, 0, 0); }
}

/* ===== Algorithms: each reports pixels through put(x, y, info) ===== */
function lineDDA(x0, y0, x1, y1, put) {
  const dx = x1 - x0, dy = y1 - y0, n = Math.max(Math.abs(dx), Math.abs(dy));
  if (!n) return put(x0, y0, { k: 0 });
  const xi = dx / n, yi = dy / n; let x = x0, y = y0;
  for (let k = 0; k <= n; k++) { put(Math.round(x), Math.round(y), { k, fx: x, fy: y }); x += xi; y += yi; }
}
function lineBres(x0, y0, x1, y1, put) {
  const dx = Math.abs(x1 - x0), dy = -Math.abs(y1 - y0), sx = x0 < x1 ? 1 : -1, sy = y0 < y1 ? 1 : -1;
  let err = dx + dy, k = 0;
  for (;;) {
    put(x0, y0, { k: k++, err });
    if (x0 === x1 && y0 === y1) break;
    const e2 = 2 * err;
    if (e2 >= dy) { err += dy; x0 += sx; }
    if (e2 <= dx) { err += dx; y0 += sy; }
  }
}
function circle(cx, cy, r, put, step) { // midpoint circle, 8-way symmetry
  let x = 0, y = r, p = 1 - r, k = 0;
  while (x <= y) {
    step && step({ k: k++, x, y, p });
    for (const [a, b] of [[x, y], [y, x], [-x, y], [-y, x], [x, -y], [y, -x], [-x, -y], [-y, -x]]) put(cx + a, cy + b);
    x++; if (p < 0) p += 2 * x + 1; else { y--; p += 2 * (x - y) + 1; }
  }
}
function ellipse(cx, cy, rx, ry, put) { // midpoint ellipse, regions 1 and 2
  const q = (x, y) => { put(cx + x, cy + y); put(cx - x, cy + y); put(cx + x, cy - y); put(cx - x, cy - y); };
  if (!rx || !ry) return lineBres(cx - rx, cy - ry, cx + rx, cy + ry, put);
  const rx2 = rx * rx, ry2 = ry * ry; let x = 0, y = ry, px = 0, py = 2 * rx2 * y, p = ry2 - rx2 * ry + 0.25 * rx2;
  while (px < py) { q(x, y); x++; px += 2 * ry2; if (p < 0) p += ry2 + px; else { y--; py -= 2 * rx2; p += ry2 + px - py; } }
  p = ry2 * (x + 0.5) ** 2 + rx2 * (y - 1) ** 2 - rx2 * ry2;
  while (y >= 0) { q(x, y); y--; py -= 2 * rx2; if (p > 0) p += rx2 - py; else { x++; px += 2 * ry2; p += rx2 - py + px; } }
}
function floodFill(R, sx, sy, c) { // scanline flood fill, 4-connected
  const { W, H, buf } = R; if (sx < 0 || sy < 0 || sx >= W || sy >= H) return;
  const t = buf[sy * W + sx]; if (t === c) return; const st = [[sx, sy]];
  while (st.length) {
    const [x, y] = st.pop(); if (buf[y * W + x] !== t) continue;
    let l = x, r = x; while (l > 0 && buf[y * W + l - 1] === t) l--; while (r < W - 1 && buf[y * W + r + 1] === t) r++;
    for (let i = l; i <= r; i++) buf[y * W + i] = c;
    for (const ny of [y - 1, y + 1]) { if (ny < 0 || ny >= H) continue; let run = false;
      for (let i = l; i <= r; i++) { const m = buf[ny * W + i] === t; if (m && !run) { st.push([i, ny]); run = true; } else if (!m) run = false; } }
  }
}

/* ===== Views: a home grid of cards, each opening one tool ===== */
const VIEWS = ['home', 'paint', 'viz', 'xf', 'd3'];
const VIEW_TITLE = { home: 'Interactive Graphics Learning Toolkit', paint: 'Mini Paint Editor', viz: 'Algorithm Visualizer', xf: '2D Transform Lab', d3: '3D Transform & Projection' };
function showView(id) {
  VIEWS.forEach(v => $('#' + v).hidden = v !== id);
  $('#backBtn').hidden = id === 'home';
  $('#toolTitle').textContent = VIEW_TITLE[id];
}
$('#backBtn').onclick = () => showView('home');
document.querySelectorAll('.card').forEach(c => c.onclick = () => {
  showView(c.dataset.view);
  if (c.dataset.view === 'viz') { $('#vmode').value = c.dataset.mode || 'bres'; vmodeChanged(); }
  else if (c.dataset.view === 'xf') tDraw();
  else if (c.dataset.view === 'd3') d3Draw();
  else if (c.dataset.view === 'paint') P.show();
});

/* ===== 1. Paint ===== */
const P = new Raster($('#c'), 640, 400);
let tool = 'pencil', color = pack('#d62828'), size = 1, algo = 'bres', hist = [], base = null, start = null, last = null, drawing = false;
const plot = (x, y, c = color) => { const r = size >> 1; for (let j = -r; j <= r; j++) for (let i = -r; i <= r; i++) P.set(x + i, y + j, c); };
const line = (a, b, c, d, col) => (algo === 'dda' ? lineDDA : lineBres)(a, b, c, d, (x, y) => plot(x, y, col));
['pencil', 'eraser', 'line', 'rect', 'circle', 'ellipse', 'fill'].forEach(t => {
  const b = document.createElement('button'); b.textContent = t; if (t === tool) b.classList.add('on');
  b.onclick = () => { tool = t; [...$('#tools').children].forEach(x => x.classList.toggle('on', x === b)); }; $('#tools').appendChild(b);
});
$('#col').oninput = e => color = pack(e.target.value);
$('#size').oninput = e => { size = +e.target.value; $('#sv').textContent = size; };
$('#algo').onchange = e => algo = e.target.value;
const snap = () => { hist.push(P.buf.slice()); if (hist.length > 40) hist.shift(); };
$('#undo').onclick = () => { if (hist.length) { P.buf.set(hist.pop()); P.show(); } };
$('#clear').onclick = () => { snap(); P.clear(); P.show(); };
$('#save').onclick = () => { const a = document.createElement('a'); a.download = 'drawing.png'; a.href = P.cv.toDataURL(); a.click(); };
const ppos = e => { const r = P.cv.getBoundingClientRect(); return [Math.floor((e.clientX - r.left) * P.W / r.width), Math.floor((e.clientY - r.top) * P.H / r.height)]; };
function shape(a, b) {
  const [x0, y0] = a, [x1, y1] = b;
  if (tool === 'line') line(x0, y0, x1, y1, color);
  else if (tool === 'rect') { line(x0, y0, x1, y0, color); line(x1, y0, x1, y1, color); line(x1, y1, x0, y1, color); line(x0, y1, x0, y0, color); }
  else if (tool === 'circle') circle(x0, y0, Math.round(Math.hypot(x1 - x0, y1 - y0)), (x, y) => plot(x, y));
  else if (tool === 'ellipse') ellipse(x0, y0, Math.abs(x1 - x0), Math.abs(y1 - y0), (x, y) => plot(x, y));
}
P.cv.addEventListener('pointerdown', e => {
  P.cv.setPointerCapture(e.pointerId); const p = ppos(e); snap();
  if (tool === 'fill') { floodFill(P, p[0], p[1], color); P.show(); return; }
  drawing = true; start = last = p; base = P.buf.slice();
  if (tool === 'pencil' || tool === 'eraser') { plot(p[0], p[1], tool === 'eraser' ? WHITE : color); P.show(); }
});
P.cv.addEventListener('pointermove', e => {
  const p = ppos(e); $('#info').textContent = `x: ${p[0]}, y: ${p[1]}  (framebuffer ${P.W}x${P.H})`; if (!drawing) return;
  if (tool === 'pencil' || tool === 'eraser') { line(last[0], last[1], p[0], p[1], tool === 'eraser' ? WHITE : color); last = p; }
  else { P.buf.set(base); shape(start, p); } P.show();
});
['pointerup', 'pointercancel'].forEach(ev => P.cv.addEventListener(ev, () => drawing = false));
P.show();

/* ===== 2. Algorithm Visualizer (magnified pixel grid, origin at centre) ===== */
const V = { cols: 24, rows: 16, cs: 28, steps: [], i: -1, timer: null, a: [], b: [] };
V.cv = $('#vc'); V.cv.width = V.cols * V.cs; V.cv.height = V.rows * V.cs; V.ctx = V.cv.getContext('2d');
const vnum = id => parseInt($('#' + id).value) || 0;
const cellXY = (x, y) => [(x + 12) * V.cs, (7 - y) * V.cs];
function vRun() {
  clearInterval(V.timer); V.timer = null; $('#vplay').textContent = 'Play';
  const m = $('#vmode').value, x0 = vnum('vx0'), y0 = vnum('vy0'), x1 = vnum('vx1'), y1 = vnum('vy1'), r = Math.max(1, vnum('vr'));
  V.mode = m; V.i = -1; V.steps = [];
  if (m === 'dda' || m === 'bres') (m === 'dda' ? lineDDA : lineBres)(x0, y0, x1, y1, (x, y, inf) => V.steps.push({ pts: [[x, y]], inf }));
  else if (m === 'circle') circle(x0, y0, r, (x, y) => V.steps[V.steps.length - 1].pts.push([x, y]), s => V.steps.push({ pts: [], inf: s }));
  else { V.a = []; V.b = []; lineDDA(x0, y0, x1, y1, (x, y) => V.a.push([x, y])); lineBres(x0, y0, x1, y1, (x, y) => V.b.push([x, y])); V.i = 0; }
  vDraw();
}
function vDraw() {
  const c = V.ctx, cs = V.cs, W = V.cv.width, H = V.cv.height, css = getComputedStyle(document.documentElement);
  const grid = css.getPropertyValue('--line'), mut = css.getPropertyValue('--muted'), acc = css.getPropertyValue('--accent');
  c.clearRect(0, 0, W, H); c.lineWidth = 1; c.strokeStyle = grid; c.beginPath();
  for (let i = 0; i <= V.cols; i++) { c.moveTo(i * cs + .5, 0); c.lineTo(i * cs + .5, H); }
  for (let j = 0; j <= V.rows; j++) { c.moveTo(0, j * cs + .5); c.lineTo(W, j * cs + .5); } c.stroke();
  c.strokeStyle = mut; c.beginPath(); c.moveTo(12.5 * cs, 0); c.lineTo(12.5 * cs, H); c.moveTo(0, 7.5 * cs); c.lineTo(W, 7.5 * cs); c.stroke();
  const m = V.mode || $('#vmode').value, x0 = vnum('vx0'), y0 = vnum('vy0'), x1 = vnum('vx1'), y1 = vnum('vy1'), r = Math.max(1, vnum('vr'));
  const ctr = (x, y) => { const [px, py] = cellXY(x, y); return [px + cs / 2, py + cs / 2]; };
  c.setLineDash([5, 4]); c.strokeStyle = mut; c.beginPath(); // ideal shape for reference only
  if (m === 'circle') { const [a, b] = ctr(x0, y0); c.arc(a, b, r * cs, 0, 7); } else { const [a, b] = ctr(x0, y0), [d, e] = ctr(x1, y1); c.moveTo(a, b); c.lineTo(d, e); }
  c.stroke(); c.setLineDash([]);
  const sum = $('#vsum'), tb = $('#vt');
  if (m === 'compare') {
    const sa = new Set(V.a.map(String)), sb = new Set(V.b.map(String));
    V.a.forEach(([x, y]) => { const [px, py] = cellXY(x, y); c.fillStyle = '#3b82f6'; c.fillRect(px + 1, py + 1, cs / 2 - 1, cs - 1); });
    V.b.forEach(([x, y]) => { const [px, py] = cellXY(x, y); c.fillStyle = '#ef4444'; c.fillRect(px + cs / 2, py + 1, cs / 2, cs - 1); });
    const diff = [...sa].filter(k => !sb.has(k)).length + [...sb].filter(k => !sa.has(k)).length;
    sum.textContent = `Blue = DDA (${sa.size} px), Red = Bresenham (${sb.size} px). Pixels that differ: ${diff}.`; tb.innerHTML = ''; return;
  }
  for (let s = 0; s <= V.i; s++) { c.fillStyle = s === V.i ? '#ef4444' : acc; c.globalAlpha = s === V.i ? 1 : .75;
    V.steps[s].pts.forEach(([x, y]) => { const [px, py] = cellXY(x, y); c.fillRect(px + 1, py + 1, cs - 1, cs - 1); }); }
  c.globalAlpha = 1;
  const head = { dda: ['k', 'x', 'y', 'real x', 'real y'], bres: ['k', 'x', 'y', 'error'], circle: ['k', 'x', 'y', 'p'] }[m];
  const cell = (m, s) => { const i = s.inf, f = n => (+n).toFixed(2); const [x, y] = s.pts[0] || [i.x, i.y];
    return m === 'dda' ? [i.k, x, y, f(i.fx), f(i.fy)] : m === 'bres' ? [i.k, x, y, i.err] : [i.k, i.x, i.y, i.p]; };
  tb.innerHTML = '<tr>' + head.map(h => `<th>${h}</th>`).join('') + '</tr>' +
    V.steps.slice(0, V.i + 1).map((s, n) => `<tr${n === V.i ? ' class="cur"' : ''}>` + cell(m, s).map(v => `<td>${v}</td>`).join('') + '</tr>').join('');
  tb.parentElement.scrollTop = 1e6;
  sum.textContent = V.i < 0 ? 'Press Step or Play.' : `Step ${V.i + 1} of ${V.steps.length}` +
    (m === 'circle' ? ' (one octant computed, the other 7 come from symmetry)' : m === 'bres' ? ' (error decides whether y moves)' : ' (round the running x, y)');
}
const vstep = () => { if (V.mode === 'compare') return; if (V.i < V.steps.length - 1) V.i++; else clearInterval(V.timer); vDraw(); };
['vx0', 'vy0', 'vx1', 'vy1', 'vr'].forEach(id => $('#' + id).onchange = vRun);
$('#vstep').onclick = vstep; $('#vreset').onclick = vRun;
$('#vall').onclick = () => { V.i = V.steps.length - 1; vDraw(); };
$('#vplay').onclick = () => { if (V.timer) { clearInterval(V.timer); V.timer = null; $('#vplay').textContent = 'Play'; return; }
  if (V.i >= V.steps.length - 1) vRun(); $('#vplay').textContent = 'Pause'; V.timer = setInterval(() => { vstep(); if (V.i >= V.steps.length - 1) { clearInterval(V.timer); V.timer = null; $('#vplay').textContent = 'Play'; } }, 450); };
$('#vline').onclick = () => { Object.entries({ vx0: 2, vy0: 2, vx1: 10, vy1: 6 }).forEach(([k, v]) => $('#' + k).value = v); if ($('#vmode').value === 'circle') $('#vmode').value = 'bres'; vRun(); };
$('#vcirc').onclick = () => { $('#vmode').value = 'circle'; $('#vx0').value = 0; $('#vy0').value = 0; $('#vr').value = 5; vRun(); };

/* ---- 2b. Area Fill visualizer (flood fill vs boundary fill, same grid/canvas) ---- */
const F = { cols: V.cols, rows: V.rows, cs: V.cs, map: new Map(), steps: [], i: -1, timer: null, seed: null };
const fKey = (x, y) => x + ',' + y;
function fBoundaryRect(x0, y0, x1, y1, map) {
  lineBres(x0, y0, x1, y0, (x, y) => map.set(fKey(x, y), 'wall')); lineBres(x1, y0, x1, y1, (x, y) => map.set(fKey(x, y), 'wall'));
  lineBres(x1, y1, x0, y1, (x, y) => map.set(fKey(x, y), 'wall')); lineBres(x0, y1, x0, y0, (x, y) => map.set(fKey(x, y), 'wall'));
}
function fScene() {
  const map = new Map(), preset = $('#fpreset').value;
  if (preset === 'rect') fBoundaryRect(3, 2, 20, 13, map);
  else if (preset === 'rect_obstacle') { fBoundaryRect(3, 2, 20, 13, map);
    for (let x = 10; x <= 13; x++) for (let y = 6; y <= 9; y++) map.set(fKey(x, y), 'obstacle'); }
  else { const pts = [[3, 2], [14, 2], [14, 7], [20, 7], [20, 13], [3, 13]];
    pts.forEach(([a, b], i) => { const [c, d] = pts[(i + 1) % pts.length]; lineBres(a, b, c, d, (x, y) => map.set(fKey(x, y), 'wall')); });
    for (let x = 5; x <= 7; x++) for (let y = 9; y <= 11; y++) map.set(fKey(x, y), 'obstacle'); }
  return map;
}
function fFillSteps(map, sx, sy, mode) { // stack-based, 4-connected, one pixel per step so it animates clearly
  const seedTag = map.get(fKey(sx, sy)) || 'bg'; if (seedTag === 'wall') return [];
  const visited = new Set(), stack = [[sx, sy]], steps = [];
  while (stack.length) {
    const [x, y] = stack.pop(); if (x < 0 || y < 0 || x >= F.cols || y >= F.rows) continue;
    const key = fKey(x, y); if (visited.has(key)) continue;
    const tag = map.get(key) || 'bg';
    if (mode === 'boundary') { if (tag === 'wall') continue; } else if (tag !== seedTag) continue; // flood fill: only same color as seed
    visited.add(key); steps.push({ x, y, k: steps.length });
    stack.push([x + 1, y], [x - 1, y], [x, y + 1], [x, y - 1]);
  }
  return steps;
}
function fDraw() {
  const c = V.ctx, cs = F.cs, W = V.cv.width, H = V.cv.height, css = getComputedStyle(document.documentElement);
  const grid = css.getPropertyValue('--line'), acc = css.getPropertyValue('--accent');
  c.clearRect(0, 0, W, H); c.lineWidth = 1; c.strokeStyle = grid; c.beginPath();
  for (let i = 0; i <= F.cols; i++) { c.moveTo(i * cs + .5, 0); c.lineTo(i * cs + .5, H); }
  for (let j = 0; j <= F.rows; j++) { c.moveTo(0, j * cs + .5); c.lineTo(W, j * cs + .5); } c.stroke();
  F.map.forEach((tag, key) => { const [x, y] = key.split(',').map(Number); const px = x * cs, py = y * cs;
    if (tag === 'wall') { c.fillStyle = '#1f2937'; c.fillRect(px, py, cs, cs); c.strokeStyle = '#111827'; c.lineWidth = 2; c.strokeRect(px + 1, py + 1, cs - 2, cs - 2); }
    else { c.fillStyle = '#f59e0b'; c.fillRect(px + 1, py + 1, cs - 1, cs - 1); } });
  for (let s = 0; s <= F.i; s++) { const p = F.steps[s]; c.fillStyle = s === F.i ? '#ef4444' : acc; c.globalAlpha = s === F.i ? 1 : .8; c.fillRect(p.x * cs + 1, p.y * cs + 1, cs - 1, cs - 1); }
  c.globalAlpha = 1;
  if (F.seed) { const [sx, sy] = F.seed; c.strokeStyle = '#ef4444'; c.lineWidth = 2; c.strokeRect(sx * cs + 2, sy * cs + 2, cs - 4, cs - 4); }
  const sum = $('#vsum'), tb = $('#vt');
  tb.innerHTML = '<tr><th>k</th><th>x</th><th>y</th></tr>' +
    F.steps.slice(0, F.i + 1).map((s, n) => `<tr${n === F.i ? ' class="cur"' : ''}><td>${s.k}</td><td>${s.x}</td><td>${s.y}</td></tr>`).join('');
  tb.parentElement.scrollTop = 1e6;
  const hasObstacle = $('#fpreset').value !== 'rect', note = hasObstacle
    ? ($('#ftype').value === 'flood' ? ' — flood fill stops at the orange obstacle (different color from the seed)' : ' — boundary fill paints over the obstacle (only the dark wall stops it)')
    : ' — flood and boundary fill give the SAME result here, because the interior is one uniform color; try a preset with an obstacle to see them diverge';
  sum.textContent = !F.seed ? 'Click inside the shape to place the seed and start filling.' + (hasObstacle ? '' : note)
    : F.i < 0 ? `Seed placed. ${F.steps.length} pixels queued — press Step or Play.`
    : `Step ${F.i + 1} of ${F.steps.length}` + note;
}
function fReset() { F.map = fScene(); F.steps = []; F.i = -1; F.seed = null; clearInterval(F.timer); F.timer = null; $('#fplay').textContent = 'Play'; fDraw(); }
const fstep = () => { if (F.i < F.steps.length - 1) F.i++; else clearInterval(F.timer); fDraw(); };
$('#fpreset').onchange = fReset; $('#ftype').onchange = () => { if (F.seed) { F.steps = fFillSteps(F.map, F.seed[0], F.seed[1], $('#ftype').value); F.i = -1; fDraw(); } };
$('#fstep').onclick = fstep; $('#freset').onclick = fReset;
$('#fall').onclick = () => { F.i = F.steps.length - 1; fDraw(); };
$('#fplay').onclick = () => { if (F.timer) { clearInterval(F.timer); F.timer = null; $('#fplay').textContent = 'Play'; return; }
  if (!F.steps.length || F.i >= F.steps.length - 1) return; $('#fplay').textContent = 'Pause';
  F.timer = setInterval(() => { fstep(); if (F.i >= F.steps.length - 1) { clearInterval(F.timer); F.timer = null; $('#fplay').textContent = 'Play'; } }, 60); };
V.cv.addEventListener('pointerdown', e => {
  if (V.mode !== 'fill') return; const r = V.cv.getBoundingClientRect();
  const gx = Math.floor((e.clientX - r.left) * V.cv.width / r.width / F.cs), gy = Math.floor((e.clientY - r.top) * V.cv.height / r.height / F.cs);
  if (gx < 0 || gy < 0 || gx >= F.cols || gy >= F.rows || F.map.get(fKey(gx, gy)) === 'wall') return;
  F.seed = [gx, gy]; F.steps = fFillSteps(F.map, gx, gy, $('#ftype').value); F.i = -1; clearInterval(F.timer); F.timer = null; $('#fplay').textContent = 'Play'; fDraw();
});

/* ---- theory + pseudocode shown below every visualizer page ---- */
const THEORY = {
  dda: {
    title: 'DDA Line Drawing — Theory',
    text: 'The Digital Differential Analyzer (DDA) is an incremental scan-conversion algorithm. It finds the number of steps needed (the larger of |dx| or |dy|), works out a constant increment for x and y per step, and rounds the running real-valued x, y to the nearest pixel at every step. It is simple to implement but uses floating-point arithmetic and rounding, which costs some speed and accuracy compared to Bresenham.',
    steps: [
      'dx = x1 − x0, dy = y1 − y0',
      'steps = max(|dx|, |dy|)',
      'xIncrement = dx / steps, yIncrement = dy / steps',
      'set (x, y) = (x0, y0)',
      'repeat steps times: plot round(x), round(y); then x += xIncrement, y += yIncrement'
    ]
  },
  bres: {
    title: "Bresenham's Line Algorithm — Theory",
    text: 'Bresenham\'s algorithm draws the same line using only integer addition, subtraction and comparison — no floating point and no rounding. It tracks a running error term that measures how far the ideal line has drifted from the last plotted pixel, and uses the sign of that error to decide whether to step the minor axis. This makes it faster and more precise than DDA, which is why it is the standard line algorithm in raster graphics.',
    steps: [
      'dx = |x1 − x0|, dy = −|y1 − y0|',
      'sx = 1 if x0 < x1 else −1,  sy = 1 if y0 < y1 else −1',
      'err = dx + dy',
      'loop: plot (x0, y0); stop if (x0, y0) = (x1, y1)',
      'e2 = 2 × err',
      'if e2 ≥ dy: err += dy, x0 += sx',
      'if e2 ≤ dx: err += dx, y0 += sy'
    ]
  },
  circle: {
    title: 'Midpoint Circle Algorithm — Theory',
    text: 'The midpoint circle algorithm exploits 8-way symmetry: a circle looks identical in each of its 8 octants, so only one octant (here, x from 0 to y, in the range 45°–90°) needs to be computed. At each step a decision parameter p tells us whether the midpoint between the two candidate next pixels lies inside or outside the true circle, which decides whether y decreases. The other 7 octants are generated for free by reflecting (x, y).',
    steps: [
      'x = 0, y = r, p = 1 − r (initial decision parameter)',
      'while x ≤ y: plot (x, y) and its 7 symmetric points about the centre',
      'x += 1',
      'if p < 0: p += 2x + 1   (midpoint is inside → stay on same y)',
      'else: y −= 1, p += 2(x − y) + 1   (midpoint is outside → move y in)'
    ]
  },
  compare: {
    title: 'DDA vs Bresenham — Why Compare',
    text: 'Both algorithms draw the exact same straight line between two points, but by different means. DDA computes a real-valued increment per axis and rounds every pixel; Bresenham replaces that rounding with a running integer error term, so it never touches a float. On most lines they agree on every pixel; where they differ, it is at the rounding boundary of a near-45° step, which is exactly the case this page highlights.',
    steps: [
      'DDA: steps = max(|dx|, |dy|); increment = dx/steps, dy/steps; round each step',
      'Bresenham: integer error term err; compare 2·err against dx and dy to decide the step',
      'Efficiency: DDA needs a float add + round per pixel; Bresenham needs only integer add/compare',
      'Accuracy: Bresenham is exact to the line equation; DDA can drift by up to half a pixel from rounding'
    ]
  },
  fill: {
    title: 'Area Filling Algorithms — Theory',
    text: 'Once a region is enclosed by a boundary, area-fill algorithms color every pixel inside it. Flood fill replaces every connected pixel that matches the seed pixel\'s original color — so it stops at any differently-colored pixel, boundary or not. Boundary fill instead keeps spreading until it hits a pixel of one specific boundary color, regardless of what color the interior pixels already are. Both are usually implemented with a stack or queue of 4-connected (or 8-connected) neighbours, exactly as this page animates. Note: the two only look different when the interior already has more than one color — against a uniform background they produce identical results, so use the "+ obstacle" presets below to see them diverge.',
    steps: [
      'push the seed pixel (sx, sy) onto a stack',
      'pop (x, y); stop this branch if it is outside the canvas or already visited',
      'Flood fill: continue only if this pixel\'s color equals the seed\'s original color',
      'Boundary fill: continue only if this pixel\'s color is not the boundary color',
      'color the pixel, mark it visited, push its 4 neighbours (up, down, left, right)',
      'repeat until the stack is empty'
    ]
  }
};
function renderTheory(mode) {
  const t = THEORY[mode]; if (!t) return;
  $('#theoryTitle').textContent = t.title;
  $('#theoryText').textContent = t.text;
  $('#theorySteps').innerHTML = t.steps.map(s => `<li>${s}</li>`).join('');
}

/* ---- mode switch between line/circle/compare and fill, sharing the same canvas + side panel ---- */
function vmodeChanged() {
  const isFill = $('#vmode').value === 'fill';
  $('#lineInputs').hidden = isFill; $('#vLineTuts').hidden = isFill; $('#fillBar').hidden = !isFill;
  V.mode = $('#vmode').value;
  renderTheory(V.mode);
  isFill ? fReset() : vRun();
}
vmodeChanged();

/* ===== 3. Transform Lab (3x3 homogeneous matrices) ===== */
const T = new Raster($('#tc'), 640, 400), U = 20, OX = 320, OY = 200;
const PRESETS = { tri: [[1, 2], [3, 5], [5, 1]], sq: [[0, 0], [0, 2], [2, 2], [2, 0]] };
const X = { pivot: [0, 0], pts: PRESETS.tri.map(p => p.slice()), drag: -1 };
const CTRL = [['tx', 'Translate X', -10, 10, 1, 0], ['ty', 'Translate Y', -8, 8, 1, 0], ['ang', 'Rotate (deg)', -180, 180, 5, 0],
  ['sx', 'Scale X', .2, 3, .1, 1], ['sy', 'Scale Y', .2, 3, .1, 1], ['shx', 'Shear X', -1.5, 1.5, .1, 0]];
CTRL.forEach(([id, name, mn, mx, st, v]) => { const d = document.createElement('div'); d.className = 'row';
  d.innerHTML = `<span>${name}</span><input type="range" id="${id}" min="${mn}" max="${mx}" step="${st}" value="${v}"><output id="o_${id}">${v}</output>`; $('#sliders').appendChild(d); });
[['rx', 'Reflect about X axis'], ['ry', 'Reflect about Y axis']].forEach(([id, t]) => { const l = document.createElement('label'); l.innerHTML = `<input type="checkbox" id="${id}"> ${t}`; $('#flips').appendChild(l); });
const mul = (a, b) => a.map((_, i) => [0, 1, 2].map(j => a[i][0] * b[0][j] + a[i][1] * b[1][j] + a[i][2] * b[2][j]));
const tr = (x, y) => [[1, 0, x], [0, 1, y], [0, 0, 1]];
const sw = (x, y) => [Math.round(OX + x * U), Math.round(OY - y * U)];

/* ---- coordinate editor: X, Y inputs per point, kept in sync with X.pts ---- */
function ptLabel(i) { return String.fromCharCode(65 + i); } // A, B, C ... matches vertex order
function renderPts() {
  const box = $('#pts'); box.innerHTML = '';
  X.pts.forEach((p, i) => {
    const row = document.createElement('div'); row.className = 'pt';
    row.innerHTML = `<span class="lbl">${ptLabel(i)}</span>
      <input type="number" step="0.5" value="${p[0]}" data-i="${i}" data-k="0">
      <input type="number" step="0.5" value="${p[1]}" data-i="${i}" data-k="1">
      <button class="sm" title="remove point">✕</button>`;
    row.querySelectorAll('input').forEach(inp => inp.oninput = e => { X.pts[i][+e.target.dataset.k] = +e.target.value || 0; tDraw(); });
    row.querySelector('button').onclick = () => { if (X.pts.length > 2) { X.pts.splice(i, 1); renderPts(); tDraw(); } };
    box.appendChild(row);
  });
}
$('#ptadd').onclick = () => { const last = X.pts[X.pts.length - 1] || [0, 0]; X.pts.push([last[0] + 1, last[1]]); $('#shape').value = 'custom'; renderPts(); tDraw(); };
$('#shape').addEventListener('input', () => { const v = $('#shape').value; if (v !== 'custom') X.pts = PRESETS[v].map(p => p.slice()); renderPts(); tDraw(); });

function tMatrix() {
  const g = id => +$('#' + id).value, a = g('ang') * Math.PI / 180, [px, py] = X.pivot;
  const Rt = [[Math.cos(a), -Math.sin(a), 0], [Math.sin(a), Math.cos(a), 0], [0, 0, 1]], Sc = [[g('sx'), 0, 0], [0, g('sy'), 0], [0, 0, 1]];
  const Sh = [[1, g('shx'), 0], [0, 1, 0], [0, 0, 1]], Rf = [[$('#ry').checked ? -1 : 1, 0, 0], [0, $('#rx').checked ? -1 : 1, 0], [0, 0, 1]];
  return [tr(g('tx'), g('ty')), tr(px, py), Rt, Sh, Rf, Sc, tr(-px, -py)].reduce((m, n) => mul(m, n));
}
function tPoly(pts, col) { const n = pts.length; for (let i = 0; i < n; i++) { const [a, b] = sw(...pts[i]), [c, d] = sw(...pts[(i + 1) % n]); lineBres(a, b, c, d, (x, y) => T.set(x, y, col)); }
  pts.forEach(p => { const [a, b] = sw(...p); for (let i = -2; i <= 2; i++) for (let j = -2; j <= 2; j++) T.set(a + i, b + j, col); }); }
function axisLabels(ctx, originX, originY, right, top, text) {
  ctx.save(); ctx.font = '600 13px ui-monospace,Menlo,monospace'; ctx.fillStyle = getComputedStyle(document.documentElement).getPropertyValue('--accent');
  ctx.fillText('X', right - 14, originY - 6); ctx.fillText('Y', originX + 6, top + 12); ctx.restore();
}
function tDraw() {
  T.clear(); const ax = pack('#c8c8c2'); lineBres(0, OY, T.W - 1, OY, (x, y) => T.set(x, y, ax)); lineBres(OX, 0, OX, T.H - 1, (x, y) => T.set(x, y, ax));
  const M = tMatrix(), src = X.pts;
  const out = src.map(([x, y]) => [M[0][0] * x + M[0][1] * y + M[0][2], M[1][0] * x + M[1][1] * y + M[1][2]]);
  tPoly(src, pack('#9a9a93')); tPoly(out, pack('#2b59ff'));
  const [a, b] = sw(...X.pivot), red = pack('#ef4444'); for (let i = -6; i <= 6; i++) { T.set(a + i, b, red); T.set(a, b + i, red); } T.show();
  axisLabels(T.ctx, OX, OY, T.W, 0);
  CTRL.forEach(([id]) => $('#o_' + id).textContent = $('#' + id).value);
  $('#mat').textContent = 'M = T · Pivot · R · Shear · Reflect · S · Pivot⁻¹\n\n' + M.map(r => r.map(v => (Math.abs(v) < 5e-10 ? 0 : v).toFixed(2).padStart(7)).join(' ')).join('\n') +
    '\n\nPoints (x, y) → (x\', y\')\n' + src.map((p, i) => `${ptLabel(i)} (${p}) → (${out[i].map(v => v.toFixed(2))})`).join('\n');
}
const xset = o => { CTRL.forEach(([id, , , , , v]) => $('#' + id).value = o[id] ?? v); $('#rx').checked = $('#ry').checked = false; X.pivot = [0, 0]; tDraw(); };
[...CTRL.map(c => c[0]), 'rx', 'ry'].forEach(id => $('#' + id).oninput = tDraw);
$('#xreset').onclick = () => xset({});
$('#ptx').onclick = () => { $('#shape').value = 'tri'; X.pts = PRESETS.tri.map(p => p.slice()); renderPts(); xset({ tx: 2, ty: 3 }); };
$('#prot').onclick = () => { $('#shape').value = 'sq'; X.pts = PRESETS.sq.map(p => p.slice()); renderPts(); xset({ ang: 90 }); };
function tcPos(e) { const r = T.cv.getBoundingClientRect(); const px = (e.clientX - r.left) * T.W / r.width, py = (e.clientY - r.top) * T.H / r.height;
  return [px, py, (px - OX) / U, -(py - OY) / U]; }
$('#tc').addEventListener('pointerdown', e => {
  T.cv.setPointerCapture(e.pointerId); const [px, py, wx, wy] = tcPos(e);
  const hit = X.pts.findIndex(p => { const [sx, sy] = sw(...p); return Math.hypot(sx - px, sy - py) < 10; });
  if (hit >= 0) { X.drag = hit; return; }
  X.pivot = [Math.round(wx * 2) / 2, Math.round(wy * 2) / 2]; tDraw();
});
$('#tc').addEventListener('pointermove', e => {
  if (X.drag < 0) return; const [, , wx, wy] = tcPos(e);
  X.pts[X.drag] = [Math.round(wx * 2) / 2, Math.round(wy * 2) / 2]; renderPts(); tDraw();
});
['pointerup', 'pointercancel'].forEach(ev => $('#tc').addEventListener(ev, () => X.drag = -1));
renderPts(); tDraw();

/* ===== 4. 3D Transform & Projection (4x4 homogeneous matrices) ===== */
const D = new Raster($('#d3c'), 640, 400), D_OX = 320, D_OY = 220, D_U = 60;
const MESH = {
  cube: { v: [[-1,-1,-1],[1,-1,-1],[1,1,-1],[-1,1,-1],[-1,-1,1],[1,-1,1],[1,1,1],[-1,1,1]],
    e: [[0,1],[1,2],[2,3],[3,0],[4,5],[5,6],[6,7],[7,4],[0,4],[1,5],[2,6],[3,7]] },
  pyramid: { v: [[-1,0,-1],[1,0,-1],[1,0,1],[-1,0,1],[0,1.4,0]],
    e: [[0,1],[1,2],[2,3],[3,0],[0,4],[1,4],[2,4],[3,4]] }
};
const D_CTRL = [['rx3', 'Rotate X (deg)', -180, 180, 5, 0], ['ry3', 'Rotate Y (deg)', -180, 180, 5, 0], ['rz3', 'Rotate Z (deg)', -180, 180, 5, 0],
  ['tx3', 'Translate X', -3, 3, .2, 0], ['ty3', 'Translate Y', -3, 3, .2, 0], ['tz3', 'Translate Z', -3, 3, .2, 0],
  ['s3', 'Uniform scale', .3, 2.5, .1, 1]];
D_CTRL.forEach(([id, name, mn, mx, st, v]) => { const d = document.createElement('div'); d.className = 'row';
  d.innerHTML = `<span>${name}</span><input type="range" id="${id}" min="${mn}" max="${mx}" step="${st}" value="${v}"><output id="o_${id}">${v}</output>`; $('#d3sliders').appendChild(d); });
// 4x4 matrix helpers: row-major, mul(A,B) = A*B
function mul4(A, B) { const R = Array.from({ length: 4 }, () => [0, 0, 0, 0]);
  for (let i = 0; i < 4; i++) for (let j = 0; j < 4; j++) for (let k = 0; k < 4; k++) R[i][j] += A[i][k] * B[k][j]; return R; }
const I4 = () => [[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]];
const tr4 = (x, y, z) => [[1,0,0,x],[0,1,0,y],[0,0,1,z],[0,0,0,1]];
const sc4 = s => [[s,0,0,0],[0,s,0,0],[0,0,s,0],[0,0,0,1]];
const rx4 = a => [[1,0,0,0],[0,Math.cos(a),-Math.sin(a),0],[0,Math.sin(a),Math.cos(a),0],[0,0,0,1]];
const ry4 = a => [[Math.cos(a),0,Math.sin(a),0],[0,1,0,0],[-Math.sin(a),0,Math.cos(a),0],[0,0,0,1]];
const rz4 = a => [[Math.cos(a),-Math.sin(a),0,0],[Math.sin(a),Math.cos(a),0,0],[0,0,1,0],[0,0,0,1]];
function apply4(M, p) { const [x, y, z] = p, w = 1;
  return [M[0][0]*x+M[0][1]*y+M[0][2]*z+M[0][3]*w, M[1][0]*x+M[1][1]*y+M[1][2]*z+M[1][3]*w, M[2][0]*x+M[2][1]*y+M[2][2]*z+M[2][3]*w]; }
// Projections: each maps a 3D point to 2D (world units, before screen scale)
function project(p, mode) {
  const [x, y, z] = p;
  if (mode === 'ortho') return [x, y];                                   // drop z
  if (mode === 'iso') { const a = Math.PI / 6;                           // classic isometric angle 30 deg
    return [(x - z) * Math.cos(a), y + (x + z) * Math.sin(a)]; }
  const k = 0.5, ang = Math.PI / 4;                                      // oblique (cavalier, 45 deg, factor 0.5)
  return [x + k * z * Math.cos(ang), y + k * z * Math.sin(ang)];
}
const d3sw = (x, y) => [Math.round(D_OX + x * D_U), Math.round(D_OY - y * D_U)];
function d3Matrix() { const g = id => +$('#' + id).value;
  return [tr4(g('tx3'), g('ty3'), g('tz3')), rz4(g('rz3') * Math.PI / 180), ry4(g('ry3') * Math.PI / 180), rx4(g('rx3') * Math.PI / 180), sc4(g('s3'))]
    .reduce((m, n) => mul4(m, n), I4());
}
function d3Draw() {
  D.clear();
  const grayAxis = pack('#c8c8c2');
  const d3axes = [[[-3,0,0],[3,0,0],'X'], [[0,-2,0],[0,2,0],'Y'], [[0,0,-3],[0,0,3],'Z']];
  d3axes.forEach(([a, b]) => {
    const [x0,y0] = d3sw(...project(a, $('#d3proj').value)), [x1,y1] = d3sw(...project(b, $('#d3proj').value));
    lineBres(x0, y0, x1, y1, (x, y) => D.set(x, y, grayAxis));
  });
  const M = d3Matrix(), mesh = MESH[$('#d3shape').value];
  const world = mesh.v.map(p => project(apply4(M, p), $('#d3proj').value));
  const col = pack('#2b59ff');
  mesh.e.forEach(([i, j]) => { const [x0, y0] = d3sw(...world[i]), [x1, y1] = d3sw(...world[j]); lineBres(x0, y0, x1, y1, (x, y) => D.set(x, y, col)); });
  world.forEach(p => { const [x, y] = d3sw(...p); for (let i = -2; i <= 2; i++) for (let j = -2; j <= 2; j++) D.set(x + i, y + j, col); });
  D.show();
  D.ctx.save(); D.ctx.font = '600 13px ui-monospace,Menlo,monospace'; D.ctx.fillStyle = getComputedStyle(document.documentElement).getPropertyValue('--accent');
  d3axes.forEach(([, b, label]) => { const [x, y] = d3sw(...project(b, $('#d3proj').value)); D.ctx.fillText(label, x + 6, y - 6); });
  D.ctx.restore();
  D_CTRL.forEach(([id]) => $('#o_' + id).textContent = $('#' + id).value);
  $('#d3mat').textContent = `M = T · Rz · Ry · Rx · S   (projection: ${$('#d3proj').value})\n\n` +
    M.map(r => r.map(v => (Math.abs(v) < 5e-10 ? 0 : v).toFixed(2).padStart(7)).join(' ')).join('\n') +
    '\n\nVertices after transform, before projection\n' + mesh.v.map((p, i) => `(${p}) → (${apply4(M, p).map(v => v.toFixed(2))})`).join('\n');
}
[...D_CTRL.map(c => c[0]), 'd3shape', 'd3proj'].forEach(id => $('#' + id).oninput = d3Draw);
$('#d3reset').onclick = () => { D_CTRL.forEach(([id, , , , , v]) => $('#' + id).value = v); d3Draw(); };
$('#d3tut').onclick = () => { $('#d3shape').value = 'cube'; D_CTRL.forEach(([id, , , , , v]) => $('#' + id).value = v); $('#rz3').value = 90; d3Draw(); };
d3Draw();
