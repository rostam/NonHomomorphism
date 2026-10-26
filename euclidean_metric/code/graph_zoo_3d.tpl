<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Graph Zoo Profiles</title>
<style>
:root{--bg:#fcfcfb;--ink:#1d1f23;--muted:#5e6470;--line:#e3e0d8;--panel:#ffffff;--edge:#4a4f57}
@media (prefers-color-scheme: dark){:root:not([data-theme="light"]){--bg:#1a1a19;--ink:#f0efec;--muted:#c3c2b7;--line:#33332f;--panel:#232321;--edge:#c3c2b7}}
:root[data-theme="dark"]{--bg:#1a1a19;--ink:#f0efec;--muted:#c3c2b7;--line:#33332f;--panel:#232321;--edge:#c3c2b7}
body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.55 system-ui,sans-serif}
.wrap{max-width:1240px;margin:0 auto;padding:24px 16px}
h1{font-size:1.55rem;margin:0 0 4px}
h2{font-size:1.15rem;margin:28px 0 8px}
p{color:var(--muted);margin:6px 0 12px}
.row{display:flex;flex-wrap:wrap;gap:8px;align-items:center;margin:8px 0}
.lbl{font-size:13px;color:var(--muted);margin-right:4px}
button,select,input{font:14px system-ui,sans-serif;background:var(--panel);color:var(--ink);border:1px solid var(--line);border-radius:6px;padding:5px 10px}
button{cursor:pointer}
button[aria-pressed="true"]{border-color:var(--ink);font-weight:600}
button[aria-pressed="false"].fam{opacity:.45}
.sw{display:inline-block;width:10px;height:10px;border-radius:50%;margin-right:6px;vertical-align:0}
.axes{display:none;grid-template-columns:repeat(3,minmax(0,1fr));gap:10px;margin:8px 0}
.axes.on{display:grid}
.axis{background:var(--panel);border:1px solid var(--line);border-radius:8px;padding:8px 10px;display:flex;gap:10px;align-items:center}
.axis .k{font:700 17px system-ui,sans-serif;width:18px}
.axis svg{flex:none;width:84px;height:84px}
.axis .info{font-size:12px;color:var(--muted);margin-top:3px}
#plot{width:100%;height:72vh;min-height:440px;background:var(--panel);border:1px solid var(--line);border-radius:8px}
.tw{overflow-x:auto;max-height:520px;overflow-y:auto;border:1px solid var(--line);border-radius:8px}
table{border-collapse:collapse;width:100%;font-size:13.5px}
th,td{border-bottom:1px solid var(--line);padding:6px 9px;text-align:left;white-space:nowrap}
th{position:sticky;top:0;background:var(--panel)}
td.num{text-align:right;font-variant-numeric:tabular-nums}
@media (max-width:760px){.axes.on{grid-template-columns:1fr}}
.measure{background:var(--panel);border:1px solid var(--line);border-left:4px solid #e34948;border-radius:8px;padding:10px 14px;margin:10px 0;font-size:14px;color:var(--ink)}
.measure ul{margin:6px 0 6px 18px;padding:0}.measure li{margin:3px 0}.measure small{color:var(--muted)}
</style>
</head>
<body>
<div class="wrap">
<h1>A zoo of graphs in the profile space</h1>
<p>Each graph G is placed by its profile φ<sub>T</sub>(G) = α(T,G)/e(T) over the 85 test cores T. Most graphs here are <b>not cores</b>: trees, grids, hypercubes, multipartite graphs, unions, products, random graphs and more. The profile depends only on the homomorphism class, so every graph lands exactly on the point of its core whenever that core is a test graph. Many graphs therefore share a point; "spread" separates them slightly. Hover for details; the table below lists where every graph lands.</p>
<div class="row" id="fams"><span class="lbl">Families</span></div>
<div class="row">
  <span class="lbl">View</span>
  <button id="vp" aria-pressed="true">PCA axes</button>
  <button id="vg" aria-pressed="false">Graphs as axes</button>
  <span class="lbl" style="margin-left:10px">Colour</span>
  <button id="cf" aria-pressed="true">by family</button>
  <button id="cc" aria-pressed="false">by χ</button>
  <span class="lbl" style="margin-left:10px">Show</span>
  <button id="bs" aria-pressed="true">Spread</button>
  <button id="bk" aria-pressed="true">Test cores</button>
  <button id="bl" aria-pressed="true">Labels</button>
  <button id="bm" aria-pressed="false">Measure distance</button>
  <button id="bz">Reset zoom</button>
  <button id="bt">Theme</button>
</div>
<div class="axes" id="axes"></div>
<div id="plot"></div>
<p id="note"></p>
<div id="measure" class="measure" hidden></div>
<h2>Where each graph lands</h2>
<div class="row"><input id="q" type="search" placeholder="Filter by name, family or landing point…" aria-label="Filter table" style="min-width:280px"></div>
<div class="tw"><table><thead><tr><th>Graph</th><th>Family</th><th>n</th><th>m</th><th>χ</th><th>ω</th><th>odd girth</th><th>Same profile as</th><th>How</th></tr></thead><tbody id="tb"></tbody></table></div>
</div>
<script src="https://cdnjs.cloudflare.com/ajax/libs/plotly.js/2.27.0/plotly.min.js"></script>
<script>
const D = {{DATA}}, SLOTS = {{SLOTS}}, SLOTS_DARK = {{SLOTS_DARK}};
const css = v => getComputedStyle(document.documentElement).getPropertyValue(v).trim();
const isDark = () => css('--bg') === '#1a1a19';
const Z = D.zoo, C = D.cores, F = D.families;
let view = 'pca', colour = 'family', spread = true, showCores = true, labels = true;
const on = F.map(() => true);
const sel = D.default.map(l => D.tests.findIndex(t => t.label === l));
const pal = () => isDark() ? SLOTS_DARK : SLOTS;
const press = (b, v) => b.setAttribute('aria-pressed', String(v));

// family chips
const fams = document.getElementById('fams');
F.forEach((f, i) => {
  const b = document.createElement('button'); b.className = 'fam'; press(b, true);
  const cnt = Z.family.filter(x => x === i).length;
  b.innerHTML = `<span class="sw" style="background:${SLOTS[i]}"></span>${f} (${cnt})`;
  b.onclick = () => { on[i] = !on[i]; press(b, on[i]); draw(); };
  fams.appendChild(b);
});
// axis pickers
const order = D.tests.map((t,i)=>i).sort((a,b) => (D.tests[b].named - D.tests[a].named) || (D.tests[a].n - D.tests[b].n));
function svgGraph(t){
  const pts = t.pos.map(([x,y]) => [42 + 34*x, 42 + 34*y]);
  return `<svg viewBox="0 0 84 84" role="img" aria-label="drawing of ${t.label}">` +
    t.edges.map(([u,v]) => `<line x1="${pts[u][0]}" y1="${pts[u][1]}" x2="${pts[v][0]}" y2="${pts[v][1]}" stroke="var(--edge)" stroke-width="1.2"/>`).join('') +
    pts.map(([x,y]) => `<circle cx="${x}" cy="${y}" r="3.2" fill="var(--panel)" stroke="var(--ink)" stroke-width="1.3"/>`).join('') + '</svg>';
}
function buildAxes(){
  const box = document.getElementById('axes'); box.innerHTML = '';
  ['X','Y','Z'].forEach((k, a) => {
    const t = D.tests[sel[a]], div = document.createElement('div'); div.className = 'axis';
    div.innerHTML = `<div class="k">${k}</div>${svgGraph(t)}<div style="min-width:0"><select aria-label="${k} axis graph">${order.map(i => `<option value="${i}" ${i===sel[a]?'selected':''}>${D.tests[i].named ? D.tests[i].label : D.tests[i].label + ' (graph6)'}</option>`).join('')}</select><div class="info">${t.n} vertices, ${t.m} edges, χ = ${t.chi}</div></div>`;
    div.querySelector('select').onchange = ev => { sel[a] = +ev.target.value; picks = []; setTimeout(resetZoom, 0); buildAxes(); draw(); };
    box.appendChild(div);
  });
}
const hash = (i, k) => { let h = (i * 2654435761 + k * 40503) >>> 0; h ^= h >>> 13; h = (h * 1274126177) >>> 0; return (h % 10007) / 10007 - 0.5; };
function coords(src, i) { return view === 'pca' ? src.pc[i] : [src.P[i][sel[0]], src.P[i][sel[1]], src.P[i][sel[2]]]; }
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
const MT = {labels: D.tests.map(t => t.label), w: D.w, m: D.tests.map(t => t.m)};
const VIEWNOTE = () => (view === 'pca' ? 'projection onto the first three principal axes' : 'uses only the three chosen test graphs') + (spread ? ', plus spread offsets' : '');
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
  const p = pal(), ink = css('--ink'), ring = css('--bg'), traces = [];
  const J = spread ? (view === 'pca' ? 0.02 : 0.025) : 0;
  if (showCores) {
    const ci = C.label.map((l,i)=>i);
    traces.push({type:'scatter3d', mode:'markers', name:'85 test cores', x: ci.map(i=>coords(C,i)[0]), y: ci.map(i=>coords(C,i)[1]), z: ci.map(i=>coords(C,i)[2]),
      _rec: ci.map(i=>({name:C.label[i], P:C.P[i]})), customdata: ci.map(i=>C.label[i]), hovertemplate:'test core <b>%{customdata}</b><extra></extra>',
      marker:{size:2.5, color: css('--muted'), opacity:0.35}});
    const cl = ci.filter(i=>C.clique[i]).sort((a,b)=> +C.label[a].slice(1) - +C.label[b].slice(1));
    traces.push({type:'scatter3d', mode:'lines+markers+text', name:'complete graphs Kₙ', x: cl.map(i=>coords(C,i)[0]), y: cl.map(i=>coords(C,i)[1]), z: cl.map(i=>coords(C,i)[2]),
      text: cl.map(i=>C.label[i]), textposition:'top center', textfont:{color:ink, size:13}, hoverinfo:'skip',
      line:{color:ink, width:3}, marker:{size:6, color: ring, line:{color:ink, width:2.5}}});
  }
  const groups = colour === 'family' ? F.map((f,i)=>({key:i, name:f, colour:p[i], test: j => Z.family[j] === i}))
    : [...new Set(Z.chi.map(c => c ?? 0))].sort((a,b)=>a-b).map(c => ({key:c, name: c ? 'χ = '+c : 'χ unknown', colour: c ? p[Math.min(c,9)-2] : css('--muted'), test: j => (Z.chi[j] ?? 0) === c}));
  const seen = {};
  groups.forEach(g => {
    const idx = Z.name.map((n,j)=>j).filter(j => on[Z.family[j]] && g.test(j));
    if (!idx.length) return;
    const xyz = idx.map(j => { const c = coords(Z, j); return [c[0] + J*hash(j,1), c[1] + J*hash(j,2), c[2] + J*hash(j,3)]; });
    const txt = idx.map(j => { const k = coords(Z,j).join('|'); if (!labels || seen[k]) return ''; seen[k] = 1; return Z.at[j] ? '' : Z.name[j]; });
    traces.push({type:'scatter3d', mode: labels ? 'markers+text' : 'markers', name: g.name,
      x: xyz.map(c=>c[0]), y: xyz.map(c=>c[1]), z: xyz.map(c=>c[2]), text: txt, textposition:'middle right', textfont:{color:ink, size:10},
      _rec: idx.map(j=>({name:Z.name[j], P:Z.P[j]})), customdata: idx.map(j => [Z.name[j], F[Z.family[j]], Z.n[j], Z.m[j], Z.chi[j] ?? '?', Z.omega[j], Z.at[j] || 'its own point', Z.exact[j] ? '' : ' (upper bounds)']),
      hovertemplate:'<b>%{customdata[0]}</b><br>%{customdata[1]}<br>n = %{customdata[2]}, m = %{customdata[3]}, χ = %{customdata[4]}, ω = %{customdata[5]}<br>same profile as: %{customdata[6]}%{customdata[7]}<extra></extra>',
      marker:{size:5, color:g.colour, opacity:0.9, symbol: idx.map(j => Z.exact[j] ? 'circle' : 'circle-open'), line:{color:ring, width:0.6}}});
  });
  const axt = i => view === 'pca' ? `PC${i+1} (${(D.var[i]*100).toFixed(0)}%)` : `${'XYZ'[i]}: φ_${D.tests[sel[i]].label}(G)`;
  const ax = i => ({title: axt(i), color:css('--muted'), gridcolor:css('--line'), zerolinecolor:css('--line'), backgroundcolor:css('--panel'), ...zoomRange(i)});
  const mt = measureTrace(); if (mt) traces.push(mt);
  lastTraces = traces;
  Plotly.react('plot', traces, {uirevision:'keep', paper_bgcolor:css('--panel'), font:{color:ink}, margin:{l:0,r:0,t:10,b:0}, legend:{x:0.01,y:0.98},
    scene:{xaxis:ax(0), yaxis:ax(1), zaxis:ax(2), aspectmode:'cube'}}, {responsive:true, displaylogo:false}).then(bindClick);
  const vis = Z.name.map((n,j)=>j).filter(j => on[Z.family[j]]);
  const pts = new Set(vis.map(j => coords(Z,j).join('|')));
  document.getElementById('note').textContent = `Click a point to zoom toward it (Reset zoom to undo); use Measure distance to compare two graphs. ${vis.length} graphs shown, at ${pts.size} distinct points. Text labels mark graphs whose profile is not that of any test core. Open circles: some coordinates are solver upper bounds (timeout).`;
}
// table
const tb = document.getElementById('tb');
Z.name.forEach((n, j) => {
  const tr = document.createElement('tr');
  tr.innerHTML = `<td>${n}</td><td><span class="sw" style="background:${SLOTS[Z.family[j]]}"></span>${F[Z.family[j]]}</td><td class="num">${Z.n[j]}</td><td class="num">${Z.m[j]}</td><td class="num">${Z.chi[j] ?? '?'}</td><td class="num">${Z.omega[j]}</td><td class="num">${Z.og[j] ?? (Z.chi[j] === 2 ? '∞' : '3')}</td><td>${Z.at[j] || '<i>its own point</i>'}</td><td>${Z.how[j]}</td>`;
  tb.appendChild(tr);
});
document.getElementById('q').oninput = ev => { const q = ev.target.value.toLowerCase(); [...tb.rows].forEach(r => r.style.display = r.textContent.toLowerCase().includes(q) ? '' : 'none'); };
// controls
const vp = document.getElementById('vp'), vg = document.getElementById('vg'), cf = document.getElementById('cf'), cc = document.getElementById('cc');
vp.onclick = () => { view='pca'; picks = []; setTimeout(resetZoom, 0); press(vp,true); press(vg,false); document.getElementById('axes').classList.remove('on'); draw(); };
vg.onclick = () => { view='graph'; picks = []; setTimeout(resetZoom, 0); press(vg,true); press(vp,false); document.getElementById('axes').classList.add('on'); draw(); };
cf.onclick = () => { colour='family'; press(cf,true); press(cc,false); draw(); };
cc.onclick = () => { colour='chi'; press(cc,true); press(cf,false); draw(); };
const tog = (id, f) => { const b = document.getElementById(id); b.onclick = () => { press(b, f()); draw(); }; };
tog('bs', () => (spread = !spread)); tog('bk', () => (showCores = !showCores)); tog('bl', () => (labels = !labels));
document.getElementById('bt').onclick = () => { const r=document.documentElement; r.dataset.theme = isDark() ? 'light' : 'dark'; buildAxes(); draw(); };
document.getElementById('bz').onclick = resetZoom;
document.getElementById('bm').onclick = toggleMeasure;
buildAxes();
if (window.Plotly) draw(); else document.getElementById('plot').textContent = 'Plotly could not load (offline?).';
</script>
</body>
</html>
