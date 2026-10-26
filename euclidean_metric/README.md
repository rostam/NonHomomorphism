# The Euclidean α-profile metric

`dist(G,H) = max(|G,H|, |H,G|)` is not a metric, and its shortest-path closure is
not Euclidean.  This folder collects the alternative: describe each graph G by
its **profile**

    φ(G) = ( w_T · |T,G| / e(T) )_T      over a family of test graphs T,

and use ordinary Euclidean distance `E(G,H) = ‖φ(G) − φ(H)‖₂`.  G is the
*target*, so φ is constant on homomorphism classes and reverses the
homomorphism order.  The earlier discussion of `dist` itself is in
`open_problems/metric_space/metric_space_review.html`.

## Start here

| File | What it is |
|---|---|
| `html/euclidean_metric_review.html` | Review page: all results, figures, GP table, agent notes (self-contained) |
| `html/alpha_profile_3d.html` | Interactive 3D view; complete graphs, circular cliques K_{p/q} and GP(n,k) highlighted (needs internet for Plotly) |
| `html/profile_axes_3d.html` | Interactive 3D view whose x, y, z axes are test graphs you choose (each axis is φ_T(G) = \|T,G\|/e(T)), with a drawing of each axis graph |
| `html/graph_zoo_3d.html` | A zoo of 136 graphs from 8 families (mostly non-cores) in the profile space: PCA or graphs-as-axes view, family filters, searchable table of where each graph lands |
| `paper/alpha_profile.pdf` | Paper draft (7 pages), source `paper/alpha_profile.tex` |

## Main results

- **Order embedding.** G → H ⇒ φ(G) ≥ φ(H). The first principal axis (92% of
  the variance) is the height in the homomorphism order.
- **Readouts.** `|K_n,G| = C(n,2) − t(n, ω(G))`; odd-cycle coordinates give the
  odd girth; `sup_T φ_T(G) = 1/ω(G)`.
- **Blind to χ.** Tests with ≤ m vertices cannot distinguish a graph of odd
  girth > m from K2. Example: 11 generalized Petersen graphs (among them the
  dodecahedron) have exactly the profile of C5 or C7 on all 85 tests, yet do
  not map to C5 or C7.
- **Farey staircase.** Each circular clique K_{p/q} that is not itself a test
  graph lands exactly on a lower circular clique with a small numerator.
  Example: K10/3 (χ = 4) has the profile of K3. The reason: χ_c of a graph
  on ≤ m vertices has numerator ≤ m.
- **Source-side profile** ψ_T(G) = 1 − s(T,G) (FJT separation) reads χ.
- **New compared with the literature:**
  - the ω-version of the clique lower bound, `|G,H| ≥ e(G) − t(|V(G)|, ω(H))`,
    which is tight for every K_n;
  - the blindness result;
  - the link to γ: `|T,H| ≤ |T,G| + μ(f)|G,H|`.

  Much of the remaining theory is in Engström–Färnqvist–Jonsson–Thapper,
  DMTCS 17:1 (2015).

## Layout

| Folder | Contents |
|---|---|
| `code/` | `alpha_profile.py` (figure and PCA 3D page), `profile_axes.py` (graphs-as-axes 3D page), `build_review.py` (review page), `gp_profiles/` (Rust: GP(n,k), circular-clique and zoo profiles), `zoo_graphs.py` + `zoo_view.py` (graph zoo), `gp_hom_check.py` (exhaustive GP → C_g check) |
| `data/` | `alpha.csv` (85 cores) and `alpha_n9.csv` (1276 cores): exact \|G,H\|, rows = source, cols = target. Also `cores_meta*.csv`, `gp_profiles.csv`, `circular_profiles.csv`, and Q's big-graph profiles |
| `figures/` | `alpha_profile_pca.png` (cliques, circular cliques and GP highlighted), R's analysis figures |
| `discussion/` | The four agents' notes (P theory, Q computation, R data analysis, S literature; 2 rounds), S's LaTeX section draft, their scripts |

## Regenerating

```bash
cd euclidean_metric/code
python alpha_profile.py      # figures/alpha_profile_pca.png, html/alpha_profile_3d.html
python profile_axes.py       # html/profile_axes_3d.html
python zoo_graphs.py         # data/zoo_graphs.txt, data/zoo_meta.csv (graphs + exact shortcuts)
python zoo_view.py           # html/graph_zoo_3d.html (needs data/zoo_profiles_computed.csv)
python build_review.py       # html/euclidean_metric_review.html
cd gp_profiles && cargo run --release -- ../../data/cores_meta.csv 20 12 > ../../data/gp_profiles.csv
cargo run --release -- circular ../../data/cores_meta.csv 20 13 8 > ../../data/circular_profiles.csv
# zoo: the graphs without a shortcut (filter zoo_graphs.txt by zoo_meta.csv), then
cargo run --release -- list ../../data/cores_meta.csv <graphs-to-compute.txt> 8 > ../../data/zoo_profiles_computed.csv
cd ../../paper && pdflatex alpha_profile.tex && pdflatex alpha_profile.tex
```
