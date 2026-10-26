<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Graphs as Axes</title>
<style>
:root{--bg:#fcfcfb;--ink:#1d1f23;--muted:#5e6470;--line:#e3e0d8;--panel:#ffffff;--edge:#4a4f57}
@media (prefers-color-scheme: dark){:root:not([data-theme="light"]){--bg:#1a1a19;--ink:#f0efec;--muted:#c3c2b7;--line:#33332f;--panel:#232321;--edge:#c3c2b7}}
:root[data-theme="dark"]{--bg:#1a1a19;--ink:#f0efec;--muted:#c3c2b7;--line:#33332f;--panel:#232321;--edge:#c3c2b7}
body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.55 system-ui,sans-serif}
.wrap{max-width:1200px;margin:0 auto;padding:24px 16px}
h1{font-size:1.5rem;margin:0 0 4px}
p{color:var(--muted);margin:6px 0 14px}
.axes{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:12px;margin:12px 0}
.axis{background:var(--panel);border:1px solid var(--line);border-radius:8px;padding:10px 12px;display:flex;gap:12px;align-items:center}
.axis .k{font:700 18px system-ui,sans-serif;width:22px}
.axis select{font:14px system-ui,sans-serif;background:var(--panel);color:var(--ink);border:1px solid var(--line);border-radius:6px;padding:4px 6px;max-width:100%}
.axis .info{font-size:13px;color:var(--muted);margin-top:4px}
.axis svg{flex:none;width:96px;height:96px}
.controls{display:flex;flex-wrap:wrap;gap:8px;margin:10px 0}
button{font:14px system-ui,sans-serif;background:var(--panel);color:var(--ink);border:1px solid var(--line);border-radius:6px;padding:6px 12px;cursor:pointer}
button[aria-pressed="true"]{border-color:var(--ink);font-weight:600}
#plot{width:100%;height:72vh;min-height:440px;background:var(--panel);border:1px solid var(--line);border-radius:8px}
@media (max-width:760px){.axes{grid-template-columns:1fr}}
</style>
</head>
<body>
<div class="wrap">
<h1>Graphs as axes</h1>
<p>Pick three test graphs T. Each graph G is placed at (φ<sub>X</sub>(G), φ<sub>Y</sub>(G), φ<sub>Z</sub>(G)), where φ<sub>T</sub>(G) = α(T,G)/e(T) is the fraction of T's edges that must be deleted before T maps into G. A coordinate is 0 exactly when T → G. Each coordinate takes only a few values, so many graphs share a point. "Spread stacked points" adds a small offset so you can see them; the highlighted families stay at their exact positions.</p>
<div class="axes" id="axes"></div>
<div class="controls">
  <button id="b8" aria-pressed="true">85 cores</button>
  <button id="b9" aria-pressed="false">1276 cores (n ≤ 9)</button>
  <button id="bj" aria-pressed="true">Spread stacked points</button>
  <button id="bc" aria-pressed="true">Circular cliques</button>
  <button id="bg" aria-pressed="true">GP(n,k)</button>
  <button id="bz">Reset zoom</button>
  <button id="bt">Toggle theme</button>
</div>
<div id="plot"></div>
<p id="note"></p>
</div>
<script src="https://cdnjs.cloudflare.com/ajax/libs/plotly.js/2.27.0/plotly.min.js"></script>
<script>
const D = {{DATA}}, SLOTS = {{SLOTS}}, SLOTS_DARK = {{SLOTS_DARK}};
const css = v => getComputedStyle(document.documentElement).getPropertyValue(v).trim();
const isDark = () => css('--bg') === '#1a1a19';
let cur = 'n8', jitter = true, showCC = true, showGP = true;
const sel = D.default.map(l => D.tests.findIndex(t => t.label === l));
const order = D.tests.map((t,i)=>i).sort((a,b) => (D.tests[b].named - D.tests[a].named) || (D.tests[a].n - D.tests[b].n) || (D.tests[a].m - D.tests[b].m));
const name = t => t.named ? t.label : `${t.label} (graph6)`;

function svgGraph(t){
  const R = 40, c = 48, pts = t.pos.map(([x,y]) => [c + R*x, c + R*y]);
  const e = t.edges.map(([u,v]) => `<line x1="${pts[u][0]}" y1="${pts[u][1]}" x2="${pts[v][0]}" y2="${pts[v][1]}" stroke="var(--edge)" stroke-width="1.3"/>`).join('');
  const p = pts.map(([x,y]) => `<circle cx="${x}" cy="${y}" r="3.6" fill="var(--panel)" stroke="var(--ink)" stroke-width="1.4"/>`).join('');
  return `<svg viewBox="0 0 96 96" role="img" aria-label="drawing of ${t.label}">${e}${p}</svg>`;
}
function buildAxes(){
  const box = document.getElementById('axes'); box.innerHTML = '';
  ['X','Y','Z'].forEach((k, a) => {
    const t = D.tests[sel[a]];
    const div = document.createElement('div'); div.className = 'axis';
    div.innerHTML = `<div class="k">${k}</div>${svgGraph(t)}<div style="min-width:0"><select aria-label="${k} axis graph">${order.map(i => `<option value="${i}" ${i===sel[a]?'selected':''}>${name(D.tests[i])}</option>`).join('')}</select><div class="info">T = ${t.label}: ${t.n} vertices, ${t.m} edges, χ = ${t.chi}</div></div>`;
    div.querySelector('select').onchange = ev => { sel[a] = +ev.target.value; setTimeout(resetZoom, 0); buildAxes(); draw(); };
    box.appendChild(div);
  });
}
const hash = (i, k) => { let h = (i * 2654435761 + k * 40503) >>> 0; h ^= h >>> 13; h = (h * 1274126177) >>> 0; return (h % 10007) / 10007 - 0.5; };
let zr = null; const ZOOM = 0.6;            // each click moves the camera 40% closer to the clicked point
const zoomRange = i => ({});                 // axis ranges stay automatic; zooming only moves the camera
const DEFAULT_CAM = {center: {x: 0, y: 0, z: 0}, eye: {x: 1.25, y: 1.25, z: 1.25}, up: {x: 0, y: 0, z: 1}};
let clickBound = false;
function bindClick(){
  const gd = document.getElementById('plot');
  if (clickBound || !gd.on) return;
  clickBound = true;
  // Plotly does not report a click on a 3D point reliably (a click looks like a zero-length rotation),
  // so treat a short, still press as a click on the point currently under the cursor.
  let hovered = null, down = null;
  gd.on('plotly_hover', ev => { const q = ev.points && ev.points[0]; hovered = q && q.x !== undefined ? q : null; });
  gd.on('plotly_unhover', () => { hovered = null; });
  gd.addEventListener('pointerdown', e => { down = {x: e.clientX, y: e.clientY, t: performance.now()}; });
  gd.addEventListener('pointerup', e => {
    const still = down && Math.hypot(e.clientX - down.x, e.clientY - down.y) < 5 && performance.now() - down.t < 600;
    down = null;
    if (!still) return;
    // Prefer the hovered point; otherwise use Plotly's own pick (it also hits lines, which send no hover events).
    const s = gd._fullLayout.scene._scene, sel = s.glplot.selection;
    // scene units: Plotly draws a data value v at v * dataScale
    const g = hovered ? [hovered.x, hovered.y, hovered.z].map((v, i) => v * s.dataScale[i])
                      : (sel && sel.dataCoordinate ? Array.from(sel.dataCoordinate) : null);
    if (g) setTimeout(() => zoomTo(gd, g), 0);
  });
}
function zoomTo(gd, g){
  // g is in scene units; layout camera units are measured from the middle of the scene box.
  const sc = gd._fullLayout.scene, b = sc._scene.glplot.bounds, cam = sc.camera;
  const c = g.map((v, i) => v - (b[0][i] + b[1][i]) / 2);
  const v = ['x', 'y', 'z'].map(k => cam.eye[k] - cam.center[k]);
  Plotly.relayout(gd, {'scene.camera.center': {x: c[0], y: c[1], z: c[2]},
                       'scene.camera.eye': {x: c[0] + v[0] * ZOOM, y: c[1] + v[1] * ZOOM, z: c[2] + v[2] * ZOOM}});
}
function resetZoom(){ Plotly.relayout(document.getElementById('plot'), {'scene.camera': DEFAULT_CAM}); }
function draw(){
  const d = D.sets[cur], pal = isDark() ? SLOTS_DARK : SLOTS, ink = css('--ink'), ring = css('--bg');
  const [xi, yi, zi] = sel, J = jitter ? 0.022 : 0;
  const co = (P, i, j, k) => P[i][j] + J * hash(i, k);
  const chis = [...new Set(d.chi)].sort((a,b)=>a-b), traces = [];
  chis.forEach(c => {
    const idx = d.chi.map((v,i)=> v===c && !d.clique[i] ? i : -1).filter(i=>i>=0);
    traces.push({type:'scatter3d', mode:'markers', name:'χ = '+c,
      x: idx.map(i=>co(d.P,i,xi,1)), y: idx.map(i=>co(d.P,i,yi,2)), z: idx.map(i=>co(d.P,i,zi,3)),
      customdata: idx.map(i=>[d.label[i], d.chi[i], d.P[i][xi], d.P[i][yi], d.P[i][zi]]),
      hovertemplate:'<b>%{customdata[0]}</b> (χ = %{customdata[1]})<br>X = %{customdata[2]:.4f}, Y = %{customdata[3]:.4f}, Z = %{customdata[4]:.4f}<extra></extra>',
      marker:{size: cur==='n8'?4:2.6, color: pal[c-2], opacity:0.65, line:{color:ring, width:0.4}}});
  });
  const cl = d.label.map((l,i)=> d.clique[i] ? i : -1).filter(i=>i>=0).sort((a,b)=> +d.label[a].slice(1) - +d.label[b].slice(1));
  traces.push({type:'scatter3d', mode:'lines+markers+text', name:'complete graphs Kₙ',
    x: cl.map(i=>d.P[i][xi]), y: cl.map(i=>d.P[i][yi]), z: cl.map(i=>d.P[i][zi]),
    text: cl.map(i=>d.label[i]), textposition:'top center', textfont:{color:ink, size:14},
    customdata: cl.map(i=>[d.label[i], d.P[i][xi], d.P[i][yi], d.P[i][zi]]),
    hovertemplate:'<b>%{customdata[0]}</b><br>X = %{customdata[1]:.4f}, Y = %{customdata[2]:.4f}, Z = %{customdata[3]:.4f}<extra></extra>',
    line:{color:ink, width:4}, marker:{size:10, color: cl.map(i=>pal[d.chi[i]-2]), line:{color:ink, width:3}}});
  const group = (F, keep) => { const g = {}; F.label.forEach((l,i) => { if (!keep(i)) return; const k = [F.P[i][xi],F.P[i][yi],F.P[i][zi]].join('|'); (g[k] = g[k] || {i, names:[]}).names.push(l); }); return Object.values(g); };
  if (showCC) {
    const C = D.circ, purple = isDark() ? '#b48cf0' : '#7a3fb0';
    traces.push({type:'scatter3d', mode:'lines', name:'circular-clique chain (by p/q)', hoverinfo:'skip',
      x: C.P.map(r=>r[xi]), y: C.P.map(r=>r[yi]), z: C.P.map(r=>r[zi]), line:{color:purple, width:4, dash:'dash'}});
    const g = group(C, i => C.q[i] > 1);
    traces.push({type:'scatter3d', mode:'markers+text', name:'circular clique K_p/q',
      x: g.map(o=>C.P[o.i][xi]), y: g.map(o=>C.P[o.i][yi]), z: g.map(o=>C.P[o.i][zi]),
      text: g.map(o=>o.names.join(', ')), textposition:'middle left', textfont:{color:purple, size:11},
      hovertemplate:'<b>%{text}</b><extra></extra>',
      marker:{size:7, symbol:'square', color: g.map(o=>pal[Math.min(C.chi[o.i],9)-2]), line:{color:purple, width:3}}});
  }
  if (showGP) {
    const G = D.gp, g = group(G, () => true);
    traces.push({type:'scatter3d', mode:'markers+text', name:'generalized Petersen GP(n,k)',
      x: g.map(o=>G.P[o.i][xi]), y: g.map(o=>G.P[o.i][yi]), z: g.map(o=>G.P[o.i][zi]),
      text: g.map(o=> o.names.length > 3 ? o.names.slice(0,3).join(', ')+` +${o.names.length-3}` : o.names.join(', ')),
      customdata: g.map(o=>o.names.join(', ')), hovertemplate:'<b>%{customdata}</b><extra></extra>',
      textposition:'middle right', textfont:{color:ink, size:11},
      marker:{size:9, symbol:'diamond-open', color:ink, line:{color:ink, width:3}}});
  }
  const t = i => D.tests[sel[i]].label;
  const ax = (i, k) => ({title:`${k}: φ_${t(i)}(G)`, color:css('--muted'), gridcolor:css('--line'), zerolinecolor:css('--line'), backgroundcolor:css('--panel'), rangemode:'tozero', ...zoomRange(i)});
  Plotly.react('plot', traces, {uirevision:'keep', paper_bgcolor:css('--panel'), font:{color:ink}, margin:{l:0,r:0,t:10,b:0}, legend:{x:0.01,y:0.98},
    scene:{xaxis:ax(0,'X'), yaxis:ax(1,'Y'), zaxis:ax(2,'Z'), aspectmode:'cube'}}, {responsive:true, displaylogo:false}).then(bindClick);
  const pts = new Set(d.P.map(r => [r[xi],r[yi],r[zi]].join('|')));
  document.getElementById('note').textContent = `Click a point to zoom toward it (Reset zoom to undo). ${d.label.length} cores occupy ${pts.size} distinct points for these three axes.` + (jitter ? ' Points are spread slightly so stacked graphs are visible; hover shows exact values.' : ' Exact positions.');
}
const press = (b, on) => b.setAttribute('aria-pressed', String(on));
const b8 = document.getElementById('b8'), b9 = document.getElementById('b9');
b8.onclick = () => { cur='n8'; press(b8,true); press(b9,false); draw(); };
b9.onclick = () => { cur='n9'; press(b9,true); press(b8,false); draw(); };
const tog = (id, f) => { const b = document.getElementById(id); b.onclick = () => { press(b, f()); draw(); }; };
tog('bj', () => (jitter = !jitter));
tog('bc', () => (showCC = !showCC));
tog('bg', () => (showGP = !showGP));
document.getElementById('bt').onclick = () => { const r=document.documentElement; r.dataset.theme = isDark() ? 'light' : 'dark'; buildAxes(); draw(); };
document.getElementById('bz').onclick = resetZoom;
buildAxes();
if (window.Plotly) draw(); else document.getElementById('plot').textContent = 'Plotly could not load (offline?).';
</script>
</body>
</html>
