# Agent R — round 1: what the Euclidean α-profile space lets us see and do

Scripts: `R_analysis.py` (all numbers; full log in `R_analysis_out.txt`), `R_extra.py` (order, segment and cluster checks), `R_figs.py` (figures).
Data: 85-core set (n ≤ 8 plus named graphs; tests are the same 85 cores) and the 1276-core n ≤ 9 set. Invariants (ω, odd girth, χ_f by LP over maximal independent sets, density, triangles per edge) are computed from graph6.

Figures (all in this folder):
- `R_axes.png`: (a) PC1–PC2 with Hasse covers of the hom order; (b) PCA inside ω ≥ 3; (c) PCA inside the triangle-free cores.
- `R_geometry.png`: (a) the K3→K4 segment, with χ-class centroids; (b) each χ-class centroid and the real core nearest to it.
- `R_clusters.png`: (a) Ward dendrogram of the 85 cores; (b) the 1276 cores coloured by Ward k=4.

## 0. A structural fact that reframes PC1: φ is order-reversing (this follows from the definition)
If G → H then α(T,H) ≤ α(T,G) for every T, so **φ(H) ≤ φ(G) coordinatewise**. When H is itself a test, the inequality is strict in coordinate H. Consequences:
- **‖φ‖₁ is a strict linear extension (height function) of the hom order.** Every PC1 loading is ≥ 0 (range 0 to 0.152), and corr(PC1, ‖φ‖₁) = 0.9997. Of the 2966 comparable pairs G→H, **0 violate PC1(G) > PC1(H)**. So the "91% triangle axis" is really **depth in the hom order**. The triangle split shows up only because the hom order has a big gap there: everything with a triangle sits below K3, and K3 is far below the triangle-free cores. See R_axes (a): all 160 Hasse covers point downward.
- **Every core that is also a test is an extreme point of the convex hull of the cloud.** Proof: if φ(G) = Σλ_H φ(H), then coordinate G forces G→H for every H in the support. So φ(H) ≤ φ(G) coordinatewise, and equality of the weighted sum forces φ(H) = φ(G). Checked by LP: 85 of 85 cores are extreme. So "extreme points = cliques and odd cycles" is **false** in full space: every core is extreme. Only the low-dimensional projections have small hulls. In the PC1–PC2 plane the hull is K2, C7, C9, C11, Grötzsch, K6–K8 plus a few n=8 cores.

## 1. Principal axes
All 85 cores (variance 91.4 / 3.1 / 1.3 / 0.8 %):
| PC | best invariant correlates | interpretation |
|---|---|---|
| PC1 | triangle-free +0.94, avg degree −0.77, χ_f −0.69 | hom-order height ≈ ‖φ‖₁ |
| PC2 | ω +0.62, χ_f +0.54, χ +0.53 | clique number (tests K4…K8 load) |
| PC3 | odd girth +0.31 | odd-cycle content: tests C5, Petersen and n=8 triangle-free cores load; separates {K2, C9, C11} from {Grötzsch, …} |
| PC4 | m +0.34, odd girth −0.24 | contrast of K3 versus C5 within the triangle-free group |
| PC5+ | weak (|r| < 0.2) | which particular 4-chromatic 7-vertex cores map in (FQyuo, GCQvRw, …) |

**Removing the triangle effect:**
- *Inside ω ≥ 3 (74 cores; 68 / 14 / 4 %).* PC1 = triangle density (r = −0.85 with triangles per edge; χ_f −0.77). PC2 = clique axis (ω −0.49; tests K4…K8). The picture in R_axes (b) is a **horseshoe**. One arm runs K3, W7 → W5, Icosahedron (ω = 3, increasingly "dense in triangles"). The other arm runs K4 → K5 → … → K8. These are two one-parameter families, not a blob.
- *Inside triangle-free (11 cores).* PC1 (81 %) correlates with **χ_f at r = +0.92**. The order is K2 (2.0), C11 (2.2), C9 (2.25), C7 (2.33), then C5 and Petersen (2.5), the 2.67 cores, and Grötzsch (2.9). The secondary axes separate Petersen from C5 (PC3 is mostly the Petersen test).
- *χ-balanced weights:* PC1 becomes 96.7 % and is still the triangle axis. Reweighting cannot remove it, because it is the order height.
- *After regressing out the ω-class means:* PC1 (52 %) correlates with m (−0.33) and is driven by W5 and the 7-vertex cores; PC2 (12.5 %) is odd girth (+0.38).

**n ≤ 9 (1276 cores; 81 / 7.6 / 2.6 %).** PC1 = triangle density and χ_f (r ≈ −0.8), PC2 = χ/ω (+0.52), PC3/PC4 = triangle-free. The 85-core picture survives.

## 2. Clustering (Ward)
- k=2 is exactly ω=2 versus ω≥3. k=4 gives {ω=2}, {ω=3 near K3, W7}, {ω=3 near W5, Icosahedron}, {ω≥4 cliques}. At k=6 the triangle-free group splits into **{K2, C7, C9, C11}** (bipartite-like, χ_f ≤ 2.33) and **{C5, Petersen, Grötzsch, …}**.
- The nearest neighbour has the same ω in 96 % of cases and the same χ in 81 %. **The space clusters by ω, not by χ.**
- n ≤ 9, Ward k=4: 16 triangle-free | 301 with ω≥4 (all of χ≥5) | **241 = ω=3 and W5 → G (100 %)** | **718 = ω=3 and W5 ↛ G (100 %)**. **Clusters are up-sets of the hom order:** they are defined by which small cores map into G (W5 and W7 have zero α in exactly the 241 group). This is visible only because the space has a centroid-based geometry.
- Most isolated cores (nearest-neighbour E): GEhrvW 0.18, GEhtvW 0.16, GEnb~g 0.15, C7 0.14, Petersen 0.13. The median is 0.07.

## 3. Geometry only Euclidean space allows
- **Centroids (the "average graph").** For χ=5 the centroid is realised: GQz^f{ is 0.056 away, within the class spread of 0.076. For χ=3 (C5 is 0.18 away, spread 0.39) and χ=4 (GCZTuW is 0.17 away, spread 0.27) the centroid is **not** near any core. These classes are not convex blobs: χ=3 mixes K3 with the odd cycles, which sit at opposite ends of PC1. The ω-class centroids are better realised (ω=2 → C5 at 0.11, ω=4 → GQyuv{ at 0.045, ω=5 → K5 at 0.02). This is again consistent with ω being the native coordinate.
- **Straight line K3 → K4 (length 0.68).** Cores sit near the ends: W7 and GCRdrs at t≈0, d=0.07; GEnbv{ and GQjRv{ at t≈1, d=0.05. **Nothing is near the middle.** The nearest core to the midpoint is 0.29 away, which is close to the half-length of 0.34. W5 and the Icosahedron project to t≈0.6 but sit 0.29 off the line. Interpolation therefore exposes a genuine **gap between K3 and K4** that is invisible with dist. Metric betweenness gives the same answer: the best near-between cores have excess ≈ 0.06–0.07 and lie at the ends.
- **Regression φ ~ invariants** (R² over all coordinates): ω one-hot **0.909**; χ one-hot 0.778; χ+ω 0.913; adding odd girth and χ_f reaches 0.937. **φ is about 91 % "ω-class + noise"**; χ adds almost nothing once ω is known.
- **Converse, invariants from φ.** ω is *exactly* readable from single coordinates: ω(G) ≥ k ⇔ φ(G)_{K_k} = 0, and odd girth ≤ 2k+1 ⇔ φ(G)_{C_{2k+1}} = 0. In regression, ω reaches LOO-exact 99 % (85 cores) and 99.8 % (n9). **χ is not linear in φ.** LOO ridge with rounding gets 91 % on the 85 cores and 99.3 % on n9 when only the 85 tests are used. The misses are all cliques (extrapolation), plus Petersen, Grötzsch, C11 and GCrb`o. {χ≤3} is **not linearly separable** with the 85-test features on n9. With all 1276 tests it is separable, but that is trivial because there are as many dimensions as points. χ_f is not recoverable (rounded hits 2 %).
- **Why χ is hidden:** φ uses G as the *target*, so it records what maps **into** G (cliques, odd cycles, W5: the up-set). χ asks what G maps **into**. A "dual" profile ψ(G) = (α(G,T)/e(G))_T would read χ directly via ψ_{K_k} = 0. **Suggestion for P/Q: the concatenation (φ, ψ) should give both ω and χ linearly.**

## Takeaways for the discussion
1. PC1 is not "triangles": it is ‖φ‖₁, a strict height function on the hom order (0 violations).
2. Every test core is an extreme point; this follows from monotonicity.
3. The geometry is organised by ω and by up-sets ("which small cores map in"), not by χ.
4. There is a real empty region between K3 and K4. The χ=3 and χ=4 class averages are not realised by any core.
5. To see χ, add the source-side profile ψ.
