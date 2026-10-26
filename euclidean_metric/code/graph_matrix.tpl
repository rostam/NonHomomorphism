<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Graphs on the Axes</title>
<style>
:root{--bg:#fcfcfb;--ink:#1d1f23;--muted:#5e6470;--line:#e3e0d8;--panel:#ffffff}
@media (prefers-color-scheme: dark){:root:not([data-theme="light"]){--bg:#1a1a19;--ink:#f0efec;--muted:#c3c2b7;--line:#33332f;--panel:#232321}}
:root[data-theme="dark"]{--bg:#1a1a19;--ink:#f0efec;--muted:#c3c2b7;--line:#33332f;--panel:#232321}
body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.55 system-ui,sans-serif}
.wrap{max-width:1240px;margin:0 auto;padding:24px 16px}
h1{font-size:1.55rem;margin:0 0 4px}
p{color:var(--muted);margin:6px 0 12px}
.row{display:flex;flex-wrap:wrap;gap:8px;align-items:center;margin:8px 0}
.lbl{font-size:13px;color:var(--muted);margin:0 2px 0 8px}
.lbl:first-child{margin-left:0}
button{font:14px system-ui,sans-serif;background:var(--panel);color:var(--ink);border:1px solid var(--line);border-radius:6px;padding:5px 10px;cursor:pointer}
button[aria-pressed="true"]{border-color:var(--ink);font-weight:600}
button:disabled{opacity:.35;cursor:default}
#plot{width:100%;height:80vh;min-height:520px;background:var(--panel);border:1px solid var(--line);border-radius:8px}
.info{background:var(--panel);border:1px solid var(--line);border-radius:8px;padding:10px 14px;margin:10px 0;font-size:14px}
</style>
</head>
<body>
<div class="wrap">
<h1>Graphs on the axes</h1>
<p>The first four metrics are computed from the profiles φ(G) = (α(T,G)/e(T))<sub>T</sub> over the 85 test graphs, so they work for every graph: Euclidean distance E, the largest single-test difference E∞, the weighted sum ℓ1, and the Färnqvist–Jonsson–Thapper metric (Hilbert projective metric on the kept fractions 1 − φ). dist and d* need α between the graphs themselves and are available only for the 85 test cores.</p>
<p>Every axis lists the graphs themselves, in a chosen order. <b>Matrix</b>: graph G on x, graph H on y, colour = d(G,H). <b>Surface</b>: the same with height z = d(G,H). <b>Triangle cube</b>: graphs G, H, K on x, y, z; a point marks a triple where d(G,K) &gt; d(G,H) + d(H,K), i.e. the triangle inequality fails, coloured by how much. For a metric the cube is empty.</p>
<div class="row">
  <span class="lbl">Data</span>
  <button data-g="set" data-v="zoo" aria-pressed="true">Zoo (314 graphs)</button>
  <button data-g="set" data-v="cores" aria-pressed="false">Test cores (85)</button>
  <span class="lbl">Metric</span>
  <button data-g="metric" data-v="E" aria-pressed="true">E (Euclidean)</button>
  <button data-g="metric" data-v="E_inf" aria-pressed="false">E∞ (max)</button>
  <button data-g="metric" data-v="L1" aria-pressed="false">ℓ1 (sum)</button>
  <button data-g="metric" data-v="FJT" aria-pressed="false">FJT (Hilbert)</button>
  <button data-g="metric" data-v="dist" aria-pressed="false">dist = max(α(G,H), α(H,G))</button>
  <button data-g="metric" data-v="d*" aria-pressed="false">d* (path closure)</button>
</div>
<div class="row">
  <span class="lbl">Order</span>
  <button data-g="order" data-v="height" aria-pressed="true">Height in hom order</button>
  <button data-g="order" data-v="chi" aria-pressed="false">χ, ω, n</button>
  <button data-g="order" data-v="family" aria-pressed="false">Family</button>
  <button data-g="order" data-v="cluster" aria-pressed="false">Clusters</button>
  <span class="lbl">View</span>
  <button data-g="view" data-v="matrix" aria-pressed="true">Matrix</button>
  <button data-g="view" data-v="surface" aria-pressed="false">Surface</button>
  <button data-g="view" data-v="cube" aria-pressed="false">Triangle cube</button>
  <button id="bt">Theme</button>
</div>
<div class="info" id="info"></div>
<div id="plot"></div>
</div>
<script src="https://cdnjs.cloudflare.com/ajax/libs/plotly.js/2.27.0/plotly.min.js"></script>
<script>
const D = {{DATA}};
const css = v => getComputedStyle(document.documentElement).getPropertyValue(v).trim();
const isDark = () => css('--bg') === '#1a1a19';
const st = {set:'zoo', metric:'E', order:'height', view:'matrix'};
const ORDER_TEXT = {height:'height in the homomorphism order (sum of the profile; complete graphs first, K2 last)',
  chi:'chromatic number, then clique number, then number of vertices', family:'family, then height',
  cluster:'average-linkage clustering of the chosen metric (similar graphs adjacent)'};
const ramp = () => isDark()
  ? [[0,'#1f2530'],[0.25,'#184f95'],[0.55,'#3987e5'],[0.8,'#86b6ef'],[1,'#e8f1fd']]
  : [[0,'#f5f9fe'],[0.2,'#cde2fb'],[0.45,'#6da7ec'],[0.7,'#2a78d6'],[1,'#0d366b']];

function sync(){
  const S = D.sets[st.set];
  if (!(st.metric in S.metrics)) st.metric = 'E';
  if (!(st.order in S.orders)) st.order = 'height';
  document.querySelectorAll('button[data-g]').forEach(b => {
    const g = b.dataset.g, v = b.dataset.v;
    b.setAttribute('aria-pressed', String(st[g] === v));
    b.disabled = (g === 'metric' && !(v in S.metrics)) || (g === 'order' && !(v in S.orders));
  });
}
function draw(){
  sync();
  const S = D.sets[st.set], M = S.metrics[st.metric], ord = S.orders[st.order], ink = css('--ink'), muted = css('--muted');
  const names = ord.map(i => S.names[i]);
  const pos = {}; ord.forEach((g, p) => pos[g] = p);
  const n = ord.length;
  const Z = ord.map(i => ord.map(j => M[i][j]));
  const flat = Z.flat(), max = Math.max(...flat);
  const zeros = flat.filter(v => v === 0).length - n;
  let info = `<b>${n} graphs</b>, metric <b>${st.metric}</b>, ordered by ${ORDER_TEXT[st.order]}. Largest distance ${Number.isInteger(max) ? max : (+max).toFixed(4)}; ${zeros / 2} pairs of different graphs are at distance 0`
    + (['E', 'E_inf', 'L1', 'FJT'].includes(st.metric) ? ' (same profile: no test graph separates them; they form solid blocks of the lowest colour along the diagonal).' : '.');
  const layoutBase = {paper_bgcolor:css('--panel'), plot_bgcolor:css('--panel'), font:{color:ink, size:11}, margin:{l:10, r:10, t:10, b:10}};
  const tick = {tickfont:{size: n > 100 ? 7 : 8, color:muted}, automargin:true, showgrid:false};
  let traces, layout;
  if (st.view === 'matrix') {
    traces = [{type:'heatmap', z:Z, x:names, y:names, colorscale:ramp(), zmin:0, zmax:max, xgap:0, ygap:0,
      colorbar:{title:{text:st.metric, side:'right'}, thickness:12, outlinewidth:0},
      hovertemplate:'G = %{x}<br>H = %{y}<br>' + st.metric + '(G,H) = %{z}<extra></extra>'}];
    layout = {...layoutBase, xaxis:{...tick, tickangle:-60, type:'category', side:'bottom', title:{text:'graph G'}},
              yaxis:{...tick, type:'category', autorange:'reversed', title:{text:'graph H'}, scaleanchor:'x'}};
  } else if (st.view === 'surface') {
    const every = Math.ceil(n / 30), tv = [...Array(n).keys()].filter(i => i % every === 0);
    const ax = t => ({title:t, tickvals:tv, ticktext:tv.map(i => names[i]), tickfont:{size:8, color:muted}, color:muted, gridcolor:css('--line'), backgroundcolor:css('--panel')});
    traces = [{type:'surface', z:Z, x:[...Array(n).keys()], y:[...Array(n).keys()], colorscale:ramp(), cmin:0, cmax:max,
      colorbar:{title:{text:st.metric}, thickness:12, outlinewidth:0},
      customdata: ord.map(i => ord.map(j => [S.names[j], S.names[i]])),
      hovertemplate:'G = %{customdata[0]}<br>H = %{customdata[1]}<br>' + st.metric + ' = %{z}<extra></extra>'}];
    layout = {...layoutBase, scene:{xaxis:ax('graph G'), yaxis:ax('graph H'), zaxis:{title:st.metric + '(G,H)', color:muted, gridcolor:css('--line'), backgroundcolor:css('--panel')},
              aspectmode:'manual', aspectratio:{x:1, y:1, z:0.5}}};
  } else {
    const V = S.violations[st.metric];
    const rows = V.rows;
    const every = Math.ceil(n / 20), tv = [...Array(n).keys()].filter(i => i % every === 0);
    const ax = t => ({title:t, range:[-1, n], tickvals:tv, ticktext:tv.map(i => names[i]), tickfont:{size:8, color:muted}, color:muted, gridcolor:css('--line'), backgroundcolor:css('--panel')});
    const dmax = rows.length ? rows[0][3] : 1;
    traces = [{type:'scatter3d', mode:'markers', name:'violations',
      x: rows.map(r => pos[r[0]]), y: rows.map(r => pos[r[1]]), z: rows.map(r => pos[r[2]]),
      customdata: rows.map(r => [S.names[r[0]], S.names[r[1]], S.names[r[2]], M[r[0]][r[2]], M[r[0]][r[1]], M[r[1]][r[2]], r[3]]),
      hovertemplate:'G = %{customdata[0]}, H = %{customdata[1]}, K = %{customdata[2]}<br>d(G,K) = %{customdata[3]} &gt; d(G,H) + d(H,K) = %{customdata[4]} + %{customdata[5]}<br>excess %{customdata[6]}<extra></extra>',
      marker:{size: n > 100 ? 2 : 2.6, color: rows.map(r => r[3]), colorscale: ramp(), cmin:0, cmax:dmax, opacity:0.75,
              colorbar:{title:{text:'excess'}, thickness:12, outlinewidth:0}}}];
    layout = {...layoutBase, scene:{xaxis:ax('G'), yaxis:ax('H (middle)'), zaxis:ax('K'), aspectmode:'cube'}};
    info += V.total
      ? ` <b>${V.total.toLocaleString()} triples break the triangle inequality</b> (G before K; each point is one triple)${V.total > rows.length ? `, the ${rows.length.toLocaleString()} worst are shown` : ''}. The largest excess is ${dmax}.`
      : ` <b>No triple breaks the triangle inequality: ${st.metric} is a metric</b>, so the cube is empty.`;
    if (!V.total) layout.annotations = [{text:`${st.metric} is a metric: no violations`, showarrow:false, xref:'paper', yref:'paper', x:0.5, y:0.5, font:{size:18, color:muted}}];
  }
  document.getElementById('info').innerHTML = info;
  Plotly.react('plot', traces, layout, {responsive:true, displaylogo:false});
}
document.querySelectorAll('button[data-g]').forEach(b => b.onclick = () => { st[b.dataset.g] = b.dataset.v; draw(); });
document.getElementById('bt').onclick = () => { const r = document.documentElement; r.dataset.theme = isDark() ? 'light' : 'dark'; draw(); };
if (window.Plotly) draw(); else document.getElementById('plot').textContent = 'Plotly could not load (offline?).';
</script>
</body>
</html>
