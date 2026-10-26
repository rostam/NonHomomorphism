# Agent R — round 2

**Scripts and outputs**
- `R_round2.py`: computations; log in `R_round2_out.txt`; numbers cached in `R2_cache.npz`.
- `R_final.py`: draws the summary figure.

**Figure:** `R_final.png`. It has three panels, and only named graphs are labelled:
- (a) the χ-balanced PCA of the 1276 cores;
- (b) ‖φ‖ against ‖ψ‖;
- (c) the B12 PCA, with Q's larger graphs projected onto it.

## (1) χ-balanced weights on the 1276 cores (Q's weights: w_T = 1/√#{tests with χ(T)})
- **Variance explained:** 91.3 / 4.5 / 1.5 %.
- **What PC1 is now:** PC1 correlates −0.93 with χ, −0.92 with ω and −0.91 with χ_f. The triangle indicator drops to 0.53. With the weights, PC1 stops being "contains a triangle" and becomes a **clique/chromatic scale**. The loadings are dominated by K7, K8 and K9, because the singleton χ-classes carry full weight.
- **PC1 is still a hom-order height.** All loadings are ≥ 0, and **0 of the 615,167 pairs G→H** violate PC1(G) > PC1(H). This is P1 again: φ reverses the order, and every non-negative linear functional of φ is monotone along it.
- **What the picture looks like (R_final a):**
  - the clique chain K9 → K4 runs as a diagonal;
  - the χ=5 cloud hangs just after K4;
  - the χ=4 / ω=3 cores form a vertical line from K3/W7 down to W5/Icosahedron (the two up-set clusters from round 1);
  - all triangle-free cores sit in a tight corner: K2 at the top, then C5/Petersen, then Grötzsch.
- **Nearest neighbours:** the nearest neighbour has the same χ in 97.1 % of cases (the same with or without weights) and the same ω in 99.8 %.
- **With B12 only** (12 tests, χ-balanced): 87.7 / 5.9 / 3.9 %. The geometry is qualitatively the same (R_final c).

## (2) The invariant source profile ψ(G)_T = max over X→G of α(X,T)/e(X)
Here X ranges over the 1276 cores and T over the same 1276 tests. This is a lower approximation of P's sup.
- **The fix matters.** ψ is strictly larger than the raw α(G,T)/e(G) in **58.6 %** of the entries. **0 monotonicity failures**: G→H implies ψ(G) ≤ ψ(H), so ψ is order-*preserving* where φ is order-reversing.
- **χ is read exactly from single coordinates:** χ(G) = min{k : ψ(G)_{K_k} = 0}. This holds on all 1276 cores, as it must, since G→K_k makes every source X→G map to K_k.
- **The norm alone sorts χ perfectly on n ≤ 9.** The mean-ψ intervals of consecutive χ-classes do not overlap, and **the top of each class is the clique K_k**. That K_k is the top follows from monotonicity. That the next class starts strictly above it is so far only empirical. So on this data **χ(G) ≤ k ⇔ ‖ψ(G)‖ ≤ ‖ψ(K_k)‖** (R_final b, dashed lines):

| χ | mean ψ | max of class |
|---|---|---|
| 3 | [0.0001, 0.0042] | K3 |
| 4 | [0.0102, 0.1294] | K4 |
| 5 | [0.1345, 0.1778] | |
| 6 | [0.17788, 0.1858] | |

  The 5/6 gap is razor thin, 6·10⁻⁵, so this is a conjecture and not robust.
- **Linear separability of {χ ≤ k} for k = 3, 4, 5** (85 test columns):

| features | separable? |
|---|---|
| φ | no |
| ψ | yes |
| the 2D plane (‖φ‖, ‖ψ‖) | yes |

- **In the ‖φ‖–‖ψ‖ plane** the 1-NN classifier gets χ right 99.1 % of the time. The cloud is an "L" shape:
  - the cliques run up the ψ-axis at φ ≈ 0;
  - the triangle-free cores lie along the φ-axis at ψ ≈ 0;
  - the χ=4 / ω=3 cores fill the corner on an anti-diagonal: Icosahedron and W5 high in ψ and low in φ, K3 and W7 the reverse.
- **Caveat.** ψ is a max over sources with n ≤ 9. For large G it is only a lower bound, and the norm-threshold law may fail once larger sources are allowed. For Mycielski-type G in particular, sources of large odd girth are needed (P8 dualised).

## (3) The five stories the user should know
1. **The main axis is the homomorphism order itself.** PC1 is, to 0.9997 correlation (unweighted), the ℓ1-norm of φ, and it never decreases along G→H: 0 violations in 615k pairs. "Triangle versus triangle-free" (unweighted) or "clique scale" (χ-balanced) are just the largest gaps in that order.
2. **φ sees ω, ψ sees χ, and the χ − ω gap is literally the 2D picture.** ω(G) ≥ k ⇔ φ_{K_k} = 0 (P4), while χ(G) ≤ k ⇔ ψ_{K_k} = 0. Plotting ‖φ‖ against ‖ψ‖ gives an L-shape, and the graphs with χ > ω (Petersen, Grötzsch, W5, Icosahedron, the odd cycles) fill the corner. On n ≤ 9, ‖ψ‖ alone orders the χ-classes with no overlap, with each class topped by its clique.
3. **The space is "lumpy": there is an empty corridor between K3 and K4.** No core lies near the middle of the K3–K4 segment: the nearest is 0.29 away against a half-length of 0.34. The χ=3 and χ=4 "average graphs" are not realised by any core. ω=3, χ=4 graphs such as W5 and Icosahedron sit *off* the line, not between K3 and K4.
4. **Clusters are up-sets: "which small graph maps into G".** On the 1276 cores, Ward clustering splits the 960 ω=3 cores exactly by whether W5 → G (241 versus 718, 100 % pure). The nearest neighbour shares ω in 96–99.8 % of cases.
5. **Big graphs collapse onto small cores in a finite basis** (Q's data, R_final c).
   - Heawood lands on K2, Dodecahedron and GP(k,2) on C5, Kneser(7,3) and Kneser(9,4) on C7 and C9.
   - Dense random G(20, .5) lands on K5, and Paley13 and Kneser(6,2) on one ω=3 point.
   - The only genuinely new points are triangle-free graphs of large χ: Kneser(8,3), Chvátal, Clebsch and Mycielski M5. They sit beyond Grötzsch in the triangle-free corner.
   - This is P8 made visible: a finite test family cannot see large χ hidden behind large odd girth. Every core is still an extreme point of the cloud (round 1).
