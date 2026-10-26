<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Alpha-Profile Space</title>
<style>
:root{--bg:#fcfcfb;--ink:#1d1f23;--muted:#5e6470;--line:#e3e0d8;--panel:#ffffff}
@media (prefers-color-scheme: dark){:root:not([data-theme="light"]){--bg:#1a1a19;--ink:#f0efec;--muted:#c3c2b7;--line:#33332f;--panel:#232321}}
:root[data-theme="dark"]{--bg:#1a1a19;--ink:#f0efec;--muted:#c3c2b7;--line:#33332f;--panel:#232321}
body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.55 system-ui,sans-serif}
.wrap{max-width:1150px;margin:0 auto;padding:24px 16px}
h1{font-size:1.5rem;margin:0 0 4px}
p{color:var(--muted);margin:6px 0 14px}
.controls{display:flex;flex-wrap:wrap;gap:8px;margin:10px 0}
button{font:14px system-ui,sans-serif;background:var(--panel);color:var(--ink);border:1px solid var(--line);border-radius:6px;padding:6px 12px;cursor:pointer}
button[aria-pressed="true"]{border-color:var(--ink);font-weight:600}
#plot{width:100%;height:74vh;min-height:440px;background:var(--panel);border:1px solid var(--line);border-radius:8px}
table{border-collapse:collapse;font-size:14px;margin-top:10px}
td,th{border-bottom:1px solid var(--line);padding:5px 10px;text-align:left;vertical-align:top}
.measure{background:var(--panel);border:1px solid var(--line);border-left:4px solid #e34948;border-radius:8px;padding:10px 14px;margin:10px 0;font-size:14px;color:var(--ink)}
.measure ul{margin:6px 0 6px 18px;padding:0}.measure li{margin:3px 0}.measure small{color:var(--muted)}
</style>
</head>
<body>
<div class="wrap">
<h1>The α-profile space of graphs</h1>
<p>Each graph G is the point φ(G) = (w<sub>T</sub>·α(T,G)/e(T))<sub>T</sub> over 85 test cores T, with χ-balanced weights w<sub>T</sub>. The distance is plain Euclidean distance, and the axes are the first three principal components. <b>Complete graphs</b> are the large circles joined by a line. <b>Generalized Petersen graphs</b> GP(n,k), 3 ≤ n ≤ 12, are the black diamonds. <b>Circular cliques</b> K<sub>p/q</sub> (p ≤ 13) are the purple-edged squares, joined by a dashed line in order of p/q. Graphs that land on the same point are listed together. Drag to rotate; hover for names.</p>
<div class="controls" role="group" aria-label="View">
  <button id="b8" aria-pressed="true">85 cores (n ≤ 8 + named)</button>
  <button id="b9" aria-pressed="false">1276 cores (n ≤ 9)</button>
  <button id="bg" aria-pressed="true">GP(n,k) on</button>
  <button id="bc" aria-pressed="true">Circular cliques on</button>
  <button id="bl" aria-pressed="true">Labels on</button>
  <button id="bm" aria-pressed="false">Measure distance</button>
  <button id="bz">Reset zoom</button>
  <button id="bt">Toggle theme</button>
</div>
<div id="plot"></div>
<p id="note"></p>
<div id="measure" class="measure" hidden></div>
<table id="gptab"><thead><tr><th>Point the GP graphs land on</th><th>Generalized Petersen graphs</th></tr></thead><tbody></tbody></table>
<table id="cctab"><thead><tr><th>Point the circular cliques land on</th><th>Circular cliques K<sub>p/q</sub></th></tr></thead><tbody></tbody></table>
</div>
<script src="https://cdnjs.cloudflare.com/ajax/libs/plotly.js/2.27.0/plotly.min.js"></script>
<script>
const DATA = {{DATA}}, SLOTS = {{SLOTS}}, SLOTS_DARK = {{SLOTS_DARK}};
let cur = 'n8', labels = true, showGP = true, showCC = true;
const css = v => getComputedStyle(document.documentElement).getPropertyValue(v).trim();
const isDark = () => css('--bg') === '#1a1a19';
// GP graphs grouped by landing point
const G = DATA.gp, groups = {};
G.label.forEach((l,i) => { const k = [G.x[i],G.y[i],G.z[i]].join('|'); (groups[k] = groups[k] || {i, names:[], at:G.equiv[i]}).names.push(l); });
const tb = document.querySelector('#gptab tbody');
Object.values(groups).forEach(g => { const tr = document.createElement('tr'); tr.innerHTML = `<td>${g.at === '-' ? '(own point)' : g.at}</td><td>${g.names.join(', ')}</td>`; tb.appendChild(tr); });
const C = DATA.circ, cgroups = {};
C.label.forEach((l,i) => { const k = [C.x[i],C.y[i],C.z[i]].join('|'); (cgroups[k] = cgroups[k] || {i, names:[], at:C.at[i]}).names.push(l); });
const tc = document.querySelector('#cctab tbody');
Object.values(cgroups).forEach(g => { const tr = document.createElement('tr'); tr.innerHTML = `<td>${g.at === '-' ? '(own point)' : g.at}</td><td>${g.names.join(', ')}</td>`; tc.appendChild(tr); });
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
    if (measure) { if (hovered) measurePick(hovered); else showMeasure('<b>Measure:</b> hover over a graph point, then click it.'); return; }
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
const MT = {labels: DATA.tests, w: DATA.w, m: DATA.tm};
const VIEWNOTE = () => 'projection onto the first three principal axes, so at most E';
// ── distance measuring: click two points; the numbers come from the full 85-test profiles ──
let measure = false, picks = [], lastTraces = [];
function measureTrace(){
  if (!picks.length) return null;
  return {type:'scatter3d', mode:'lines+markers', name:'measured', showlegend:false, hoverinfo:'skip',
    x: picks.map(p=>p.xyz[0]), y: picks.map(p=>p.xyz[1]), z: picks.map(p=>p.xyz[2]),
    line:{color:'#e34948', width:6}, marker:{size:10, color:'#e34948', symbol:'circle-open', line:{color:'#e34948', width:3}}};
}
function showMeasure(html){ const m = document.getElementById('measure'); m.hidden = false; m.innerHTML = html; }
function measurePick(pt){
  const tr = lastTraces[pt.curveNumber], rec = tr && tr._rec && tr._rec[pt.pointNumber];
  if (!rec) { showMeasure('<b>Measure:</b> click on a graph point (lines cannot be measured).'); return; }
  if (picks.length >= 2) picks = [];
  picks.push({name: rec.name, P: rec.P, xyz: [pt.x, pt.y, pt.z]});
  if (picks.length === 1) showMeasure(`<b>Measure:</b> first point <b>${rec.name}</b>. Now click a second point.`);
  else reportMeasure();
  draw();
}
function reportMeasure(){
  const [A, B] = picks, T = MT.labels, n = T.length, f = v => (+v).toFixed(4);
  const diff = A.P.map((v, t) => v - B.P[t]);
  const E = Math.sqrt(diff.reduce((s, d, t) => s + (MT.w[t] * d) ** 2, 0));
  const E2 = Math.sqrt(diff.reduce((s, d) => s + d * d, 0));
  let ti = 0; diff.forEach((d, t) => { if (Math.abs(d) > Math.abs(diff[ti])) ti = t; });
  const nz = diff.filter(d => Math.abs(d) > 1e-9).length;
  const scr = Math.hypot(...A.xyz.map((v, i) => v - B.xyz[i]));
  const alpha = (P, t) => Math.round(P[t] * MT.m[t]);
  const top = diff.map((d, t) => [Math.abs(MT.w[t] * d), t]).filter(x => x[0] > 1e-9).sort((a, b) => b[0] - a[0]).slice(0, 6);
  // a point may stand for several graphs with the same profile ("K4, K13/3, K9/2"); use a member that is a test graph
  const asTest = r => { const m = r.name.split(', ').find(x => T.includes(x)); return m ? [m, T.indexOf(m)] : [null, -1]; };
  const [na, ia] = asTest(A), [nb, ib] = asTest(B);
  const dist = ia >= 0 && ib >= 0 ? `<li><b>dist</b> = max(α(${na},${nb}), α(${nb},${na})) = max(${alpha(B.P, ia)}, ${alpha(A.P, ib)}) = <b>${Math.max(alpha(B.P, ia), alpha(A.P, ib))}</b>: the original (non-metric) distance, available because both are test graphs</li>` : '';
  showMeasure(`<b>Distance between ${A.name} and ${B.name}</b>
  <ul>
   <li><b>Profile distance E = ${f(E)}</b> (Euclidean over all ${n} test graphs, χ-balanced weights)${E < 1e-9 ? ': identical profiles, no test graph separates them' : ''}</li>
   <li>Unweighted: ${f(E2)} · largest single-test difference ${f(Math.abs(diff[ti]))} (test ${T[ti]})</li>
   <li>On screen: ${f(scr)} (${VIEWNOTE()})</li>
   <li>${nz} of ${n} test graphs separate them${top.length ? '. Largest contributions: ' + top.map(([, t]) => `${T[t]}: α = ${alpha(A.P, t)} vs ${alpha(B.P, t)}`).join('; ') : ''}</li>
   ${dist}
  </ul>
  <small>φ<sub>T</sub>(G) = α(T,G)/e(T) is the fraction of T's edges lost when T is mapped into G. E uses the full profiles, so it does not depend on the view or on spread offsets.</small>`);
}
function toggleMeasure(){
  measure = !measure; picks = [];
  const b = document.getElementById('bm'); b.setAttribute('aria-pressed', String(measure));
  if (measure) showMeasure('<b>Measure:</b> click two graph points.'); else document.getElementById('measure').hidden = true;
  draw();
}
function draw(){
  const d = DATA.sets[cur], pal = isDark() ? SLOTS_DARK : SLOTS, chis = [...new Set(d.chi)].sort((a,b)=>a-b);
  const ring = css('--bg'), ink = css('--ink');
  const traces = chis.map(c => {
    const idx = d.chi.map((v,i)=> v===c && !d.clique[i] ? i : -1).filter(i=>i>=0);
    return {type:'scatter3d', mode: labels ? 'markers+text' : 'markers', name:'χ = '+c,
      x: idx.map(i=>d.x[i]), y: idx.map(i=>d.y[i]), z: idx.map(i=>d.z[i]),
      text: idx.map(i=> labels && d.named[i] ? d.label[i] : ''), textposition:'bottom center',
      textfont:{color:css('--muted'), size:10},
      _rec: idx.map(i=>({name:d.label[i], P:d.P[i]})), customdata: idx.map(i=>[d.label[i], d.chi[i], d.n[i], d.m[i]]),
      hovertemplate:'<b>%{customdata[0]}</b><br>χ = %{customdata[1]}, n = %{customdata[2]}, m = %{customdata[3]}<extra></extra>',
      marker:{size: cur==='n8'?4:2.5, color: pal[c-2], opacity:0.6, line:{color:ring, width:0.5}}};
  });
  const cl = d.label.map((l,i)=> d.clique[i] ? i : -1).filter(i=>i>=0).sort((a,b)=> +d.label[a].slice(1) - +d.label[b].slice(1));
  traces.push({type:'scatter3d', mode:'lines+markers+text', name:'complete graphs Kₙ',
    x: cl.map(i=>d.x[i]), y: cl.map(i=>d.y[i]), z: cl.map(i=>d.z[i]),
    text: cl.map(i=>d.label[i]), textposition:'top center', textfont:{color:ink, size:15},
    _rec: cl.map(i=>({name:d.label[i], P:d.P[i]})), customdata: cl.map(i=>[d.label[i], d.chi[i]]),
    hovertemplate:'<b>%{customdata[0]}</b> (complete graph)<extra></extra>',
    line:{color:ink, width:4}, marker:{size:11, color: cl.map(i=>pal[d.chi[i]-2]), line:{color:ink, width:3}}});
  if (showCC) {
    const purple = isDark() ? '#b48cf0' : '#7a3fb0';
    traces.push({type:'scatter3d', mode:'lines', name:'circular-clique chain (by p/q)', x:C.x, y:C.y, z:C.z,
      line:{color:purple, width:4, dash:'dash'}, hoverinfo:'skip'});
    const cg = Object.values(cgroups).filter(g => g.names.some(n => n.includes('/')));
    traces.push({type:'scatter3d', mode: labels ? 'markers+text' : 'markers', name:'circular clique K_p/q',
      x: cg.map(g=>C.x[g.i]), y: cg.map(g=>C.y[g.i]), z: cg.map(g=>C.z[g.i]),
      text: cg.map(g=> g.names.filter(n => n.includes('/')).join(', ')), textposition:'middle left', textfont:{color:purple, size:11},
      _rec: cg.map(g=>({name:g.names.join(', '), P:C.P[g.i]})), customdata: cg.map(g=>[g.names.join(', '), g.at]),
      hovertemplate:'<b>%{customdata[0]}</b><br>same profile as: %{customdata[1]}<extra></extra>',
      marker:{size:7, symbol:'square', color: cg.map(g=>pal[Math.min(C.chi[g.i], 9)-2]), line:{color:purple, width:3}}});
  }
  if (showGP) {
    const gs = Object.values(groups);
    traces.push({type:'scatter3d', mode: labels ? 'markers+text' : 'markers', name:'generalized Petersen GP(n,k)',
      x: gs.map(g=>G.x[g.i]), y: gs.map(g=>G.y[g.i]), z: gs.map(g=>G.z[g.i]),
      text: gs.map(g=> g.names.length > 3 ? g.names.slice(0,3).join(', ')+` +${g.names.length-3}` : g.names.join(', ')),
      textposition:'middle right', textfont:{color:ink, size:11},
      _rec: gs.map(g=>({name:g.names.join(', '), P:G.P[g.i]})), customdata: gs.map(g=>[g.names.join(', '), g.at]),
      hovertemplate:'<b>%{customdata[0]}</b><br>same profile as: %{customdata[1]}<extra></extra>',
      marker:{size:9, symbol:'diamond-open', color:ink, line:{color:ink, width:3}}});
  }
  const ax = i => ({title:`PC${i+1} (${(DATA.var[i]*100).toFixed(0)}%)`, color:css('--muted'), gridcolor:css('--line'), zerolinecolor:css('--line'), backgroundcolor:css('--panel'), ...zoomRange(i)});
  const mt = measureTrace(); if (mt) traces.push(mt);
  lastTraces = traces;
  Plotly.react('plot', traces, {uirevision:'keep', paper_bgcolor:css('--panel'), font:{color:ink}, margin:{l:0,r:0,t:10,b:0},
    legend:{x:0.01,y:0.98}, scene:{xaxis:ax(0), yaxis:ax(1), zaxis:ax(2), aspectmode:'cube'}}, {responsive:true, displaylogo:false}).then(bindClick);
  document.getElementById('note').textContent = `Click a point to zoom toward it (Reset zoom to undo); use Measure distance to compare two graphs. ${d.label.length} cores, ${G.label.length} generalized Petersen graphs and ${C.label.length} circular cliques. The axes are fixed by the 85-core configuration; the first three carry ${((DATA.var[0]+DATA.var[1]+DATA.var[2])*100).toFixed(1)}% of its variance.`;
}
const press = (b, on) => b.setAttribute('aria-pressed', String(on));
const bc = document.getElementById('bc');
bc.onclick = () => { showCC=!showCC; press(bc,showCC); bc.textContent = showCC?'Circular cliques on':'Circular cliques off'; draw(); };
const b8 = document.getElementById('b8'), b9 = document.getElementById('b9'), bg = document.getElementById('bg'), bl = document.getElementById('bl');
b8.onclick = () => { cur='n8'; press(b8,true); press(b9,false); draw(); };
b9.onclick = () => { cur='n9'; press(b9,true); press(b8,false); draw(); };
bg.onclick = () => { showGP=!showGP; press(bg,showGP); bg.textContent = showGP?'GP(n,k) on':'GP(n,k) off'; draw(); };
bl.onclick = () => { labels=!labels; press(bl,labels); bl.textContent = labels?'Labels on':'Labels off'; draw(); };
document.getElementById('bt').onclick = () => { const r=document.documentElement; r.dataset.theme = isDark() ? 'light' : 'dark'; draw(); };
document.getElementById('bz').onclick = resetZoom;
document.getElementById('bm').onclick = toggleMeasure;
if (window.Plotly) draw(); else document.getElementById('plot').textContent = 'Plotly could not load (offline?).';
</script>
</body>
</html>
