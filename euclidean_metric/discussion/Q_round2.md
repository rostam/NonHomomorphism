# Q: round 2 (data)

Scripts:
- `Q_crate` (`q_profiles 20 gm`) → `Q_gm.csv`
- `Q_round2.py` → `Q_round2_out.md`
- `Q_3col.py`, a naive 3-colouring check that timed out

Total compute was about 15 min, of which about 10 min was the abandoned colouring check.

## (1a) P8 in data: graphs with χ = 4 that look like K2 or C5

μ_r(C_{2k+1}) is the generalized Mycielskian with r layers. It has odd girth 2k+1 (computed), and χ = 4 for every r by Stiebitz's theorem. My naive 3-colouring search could not finish on 92 vertices, so χ = 4 here rests on the theorem, not on computation.

Each row gives the B12 profile as raw α: K2 K3 K4 K5 K6 | C5 C7 C9 | Pet Grö W5 Ico.

| target | n | m | og | χ | B12 profile | equals φ_B12 of |
|---|---|---|---|---|---|---|
| μ₂(C5) | 16 | 30 | 5 | 4 | 0 1 2 4 6 \| 0 0 0 \| 2 3 3 10 | **C5** |
| μ₃(C7) | 29 | 56 | 7 | 4 | 0 1 2 4 6 \| 1 0 0 \| 3 4 3 10 | **C7** |
| μ₄(C9) | 46 | 90 | 9 | 4 | 0 1 2 4 6 \| 1 1 0 \| 3 4 3 10 | **C9** |
| μ₅(C11) | 67 | 132 | 11 | 4 | 0 1 2 4 6 \| 1 1 1 \| 3 4 3 10 | **K2** |
| μ₆(C13) | 92 | 182 | 13 | 4 | 0 1 2 4 6 \| 1 1 1 \| 3 4 3 10 | **K2**: exact for *every* test with ≤ 12 vertices (P8) |
| μ₆(C13) ⊔ C5, also with a bridge | 97 | 187/188 | 5 | 4 | 0 1 2 4 6 \| 0 0 0 \| 2 3 3 10 | **C5**: exact for every test with ≤ 12 vertices |

Notes on the table:
- The Grötzsch and Icosahedron entries on targets of odd girth ≥ 11 timed out at 20 s. They are exact by argument:
  - Icosahedron: on any triangle-free target, 20 triangles with each edge in 2 force α ≥ 10, and α(Ico,K2) = 10.
  - Grötzsch: P8 gives α(Grö, μ₆(C13)) = α(Grö,K2) = 4.
  - For the ⊔C5 graphs the true value is 3, and the solver's upper bound of 4 is not tight. Argument: an image with ≤ 12 vertices meets μ in a bipartite part attached to C5 through at most one cut vertex, so it maps to C5. So α(T, μ⊔C5) = α(T, C5) for |T| ≤ 12.
- **General statement (P8, extended):** if og(G) > m, then φ_𝒯(G ⊔ H) = φ_𝒯(K2 ⊔ H) for every test family 𝒯 of graphs with ≤ m vertices. The same holds with a bridge between G and H.
  - Taking G to be an Erdős graph (large χ, large girth), a fixed finite test family therefore gives **the same profile as K2, or as C5, or as any H, at arbitrary χ**.
  - The smallest witness I have for B12 is μ₅(C11), with 67 vertices and χ = 4. Its profile equals φ(K2) on all 12 basis tests.

## (1b) Source-side ψ(G)_T = max over X→G (X in pool) of α(X,T)/e(X), for T ∈ {K2,…,K5}

ψ depends only on the hom class of G. My χ estimate is the least k with ψ_{K_k}(G) = 0.

| pool of sources X | pool size | χ exact (χ capped at 6) | misses by true χ |
|---|---|---|---|
| all 1276 cores (contains G itself) | 1276 | **1276/1276** | none |
| 85 cores | 85 | 920/1276 | χ=4: 113, χ=5: 236, χ=6: 7 |
| cores with n ≤ 8 | 80 | 906 | 4: 125, 5: 236 |
| cores with n ≤ 7 | 17 | 798 | 4: 196, 5: 272 |
| B12 | 12 | 558 | 4: 423, 5: 286 |
| cores with n ≤ 5 | 5 | 15 | almost all |

- ψ recovers χ **exactly when the pool contains G, or a graph X → G with χ(X) = χ(G)**. That is just χ(G) = max{χ(X) : X → G}, so it is a tautology once G is in the pool.
- With any fixed small pool, ψ only gives a lower bound on χ (each miss underestimates χ).
- This is the source-side mirror of P8: a bounded source pool cannot certify large χ, because the 4-chromatic μ_r(C_{2k+1}) has no small 4-chromatic subgraph.
- The concatenation (φ, ψ) therefore sees χ only through "large" coordinates on both sides.

## (2) Recommended default α-profile metric

Targets: the 1276 cores. Merged pairs are exact counts from integer α.

| tests, weights | E~dist (Pearson/Spearman) | E~d* | E~d_n | merged pairs | ρ vs recommended |
|---|---|---|---|---|---|
| all 1276, unweighted | .777/.788 | .586/.752 | .847/.655 | 0 | .962 |
| **all 1276, χ-balanced** | **.915/.855** | **.829/.830** | .918/.698 | **0** | 1 |
| all 1276, χ-bal·e(T)^{-1/2} | .902/.854 | .791/.829 | **.922**/.703 | 0 | .999 |
| all 1276, w = 1/e(T) | .740/.752 | .538/.713 | .823/.631 | 0 | .937 |
| 85 tests, χ-balanced | .910/.850 | .822/.830 | .917/.716 | 39,540 | .991 |
| B12, χ-balanced | .899/.849 | .820/.832 | .907/.746 | 188,543 | .935 |

**Recommendation.**
- **Default:** tests = all connected cores up to the size of the targets, weights w_T = 1/√N_{χ(T)}, so each χ class of tests carries equal total squared weight.
  - It is the best on dist and d* among all variants tried.
  - It is a genuine metric on the cores it covers (P1 plus 0 merged pairs).
  - It is stable: dropping any one test gives Spearman ρ ≥ .9995.
- **Cheap version:** the 85 n≤8 tests, χ-balanced.
  - It has ρ = .991 with the default and the same correlations.
  - It is only a pseudometric on n=9: 39,540 merged pairs out of 813k.
  - Leave-one-test-out gives min ρ = .9993.
- **Avoid:** B12 alone (16 classes) and 1/e(T) weighting (it worsens every correlation).
- **Caveat to state:** any finite family gives a pseudometric on larger graphs (separating n ≤ 9 alone needs ≥ 253 tests) and is χ-blind (1a).

## (3) S's closed forms: all confirmed on the 1276 cores

- α(K_k,G) = C(k,2) − t(k, min(k,ω(G))) for k = 2..9: **10,208 / 10,208** entries agree. Here ω is computed from graph6.
- α(C_{2k+1},G) ∈ {0,1}, with 0 iff og(G) ≤ 2k+1, for C5, C7, C9, C11: **5,104 / 5,104** agree. So φ_{C_{2k+1}} ∈ {0, 1/(2k+1)}.
- α(Petersen, C5) = 2, so φ = **2/15** ✓.
- The large targets in `Q_profiles.csv` agree as well. Examples: K-coordinates (1,2,4,6) on all triangle-free targets, and C-coordinates that switch exactly at the odd girth (K(7,3): og 7; K(9,4): og 9).
