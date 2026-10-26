# Q (computational experimenter): round 1

Notation: φ_F(G) = (α(T,G)/e(T))_{T∈F}; E_F(G,H) = ||φ_F(G) − φ_F(H)||₂. dist = max(α, αᵀ), d* = its shortest-path closure, d_n = edge-normalized dist (matrices from `../discussion/`).
Basis **B12** = {K2, K3, K4, K5, K6, C5, C7, C9, Petersen, Grötzsch, W5, Icosahedron}. α(K2,·) ≡ 0 on any target with an edge, so B12 is effectively 11 tests.
χ-balanced means test weight w_T = 1/√(number of tests with χ(T)), so every χ class carries total squared weight 1.

Scripts: `Q_testfamily.py` (tasks 1 and 3; output in `Q_testfamily_out.md`), `Q_forced.py` (separation bounds), `Q_crate/` (Rust, task 2), `Q_post.py` → `Q_profiles.csv`.

## 1. Test-family design

### Dimension and agreement with the existing distances (correlations are Pearson/Spearman over all pairs)

| targets | family | #tests | eff. dim (PR) | PC1 | #PCs for 99% | E~dist | E~d* | E~d_n | distinct profiles |
|---|---|---|---|---|---|---|---|---|---|
| 85 cores | all | 85 | 1.19 | 91% | 13 | .76/.82 | .54/.75 | .91/.78 | 85 |
| 85 | all, χ-balanced | 85 | 1.17 | 92% | 6 | **.87/.86** | **.75/.81** | **.96/.82** | 85 |
| 85 | B12 | 12 | 1.33 | 86% | 6 | .81/.86 | .64/.81 | .95/.84 | **15** |
| 85 | B12, χ-balanced | 12 | 1.20 | 91% | 5 | .85/.87 | .72/.81 | .96/.84 | 15 |
| 85 | triangle-free tests only | 11 | 1.34 | 86% | 7 | .53/.50 | .30/.37 | .70/.56 | 13 |
| 1276 cores | all | 1276 | 1.49 | 81% | 54 | .78/.79 | .59/.75 | .85/.66 | 1276 |
| 1276 | all, χ-balanced | 1276 | 1.20 | 91% | 10 | **.92/.86** | **.83/.83** | .92/.70 | 1276 |
| 1276 | B12 | 12 | 1.53 | 80% | 6 | .87/.85 | .78/.83 | .89/.73 | **16** (188,543 pairs at E=0) |
| 1276 | B12, χ-balanced | 12 | 1.29 | 88% | 5 | .90/.85 | .82/.83 | .91/.75 | 16 |
| 1276 | triangle-free tests only | 16 | 1.79 | 72% | 7 | .41/.13 | .19/.08 | .53/.15 | 18 |

In every row the participation ratio is 1.2 to 1.8, so the one-dominant-axis picture does not come from the 74/85 triangle bias. That axis is a "chromatic/clique scale".

χ-balancing makes the agreement with dist and d* clearly better. On the 1276 cores, Pearson E~d* goes from .59 to .83. It also shrinks the spectral tail (54 → 10 PCs for 99%).

B12 gives about the same correlation as all tests at 1% of the cost. However, it collapses the 1276 cores into only 16 classes, so E_{B12} is only a pseudometric.

Spearman agreement between families: E_{B12} vs E_all is .937 (85 cores) and .914 (1276 cores). E_all vs E_all,χ-balanced is .967 and .962.

### Separation: there is no small separating set

- **253** of the 813,450 core pairs (n≤9) are separated by **exactly one** test, and in every case that test is one of the two graphs themselves. Each of these 253 tests is therefore forced, so **any separating family has ≥ 253 tests**.
  - On the 85 cores the same argument forces 37 tests.
- Typical forced pair: a 4-chromatic 8-vertex core T and K3. Here α(T,K3)=1, and α(S,T)=α(S,K3) for every other core S.
- Upper bounds:
  - Greedy over all cores: **321** tests separate all 1276 cores.
  - The 253 forced tests plus a greedy completion: **311**.
  - So the minimum lies in **[253, 311]** (n≤9) and **[37, 42]** (85 cores).
  - The information bound (≤ 8 distinct values per test) would only require 4.
- Restricted candidate pools never separate all cores:

| pool | greedy size | merged pairs left (1276 cores) |
|---|---|---|
| tests with n ≤ 6 | 3 | 327,482 |
| tests with n ≤ 7 | 10 | 94,661 |
| tests with n ≤ 8 | 60 | 40,985 |
| B12 | 7 | 188,543 |
| all non-complete cores | 320 | 6 |

  The 6 merged pairs come from complete targets, which only K_k tests can tell apart.

## 2. Profiles of larger graphs (B12; `Q_profiles.csv`)

Exact branch and bound in `Q_crate`:
- symmetry reduction: one vertex is fixed for vertex-transitive targets, and an arc is fixed for arc-transitive ones;
- a per-vertex lookahead bound and a local-search upper bound;
- checked against the repo `nonhom_param` on all small pairs, with 0 mismatches.

Six cases (Icosahedron into a triangle-free target) hit the 6 s limit with upper bound 10. They are exact by a short argument: Icosahedron has 20 triangles and each edge lies in 2 of them, so at least 10 edges must go; and α(Ico,K2)=10.

Total run time was about 3 minutes.

Each row of the table below gives α(T,G) for T = K2 K3 K4 K5 K6 | C5 C7 C9 | Pet Grö W5 Ico.

| profile class (raw α) | targets with that B12 profile |
|---|---|
| 0 1 2 4 6 \| 1 1 1 \| 3 4 3 10 (= K2) | K2, Heawood, C13, C15 |
| 0 1 2 4 6 \| 0 0 0 \| 2 3 3 10 (= C5) | C5, dodecahedron, GP(7,2), GP(9,2), GP(11,2), Circ(14;1,4), G(30,.1) |
| 0 1 2 4 6 \| 1 0 0 \| 3 4 3 10 | Kneser(7,3) (= C7's profile) |
| 0 1 2 4 6 \| 1 1 0 \| 3 4 3 10 | Kneser(9,4) (= C9's profile) |
| 0 1 2 4 6 \| 0 0 0 \| 0 3 3 10 | Petersen |
| 0 1 2 4 6 \| 0 0 0 \| 0 2 3 10 | Kneser(8,3) (new; no n≤9 core matches) |
| 0 1 2 4 6 \| 0 0 0 \| 1 2 3 10 | Circ(13;1,5) |
| 0 1 2 4 6 \| 0 0 0 \| 1 1 3 10 | Chvátal, Circ(16;1,3,8) (new) |
| 0 1 2 4 6 \| 0 0 0 \| 1 0 3 10 | Grötzsch |
| 0 1 2 4 6 \| 0 0 0 \| 0 0 3 10 | Mycielski M5, Clebsch (new) |
| 0 0 1 2 3 \| 0 \| 0 1 1 3 (= K3) | K3, C11², G(20,.2)#2, G(40,.1) |
| 0 0 1 2 3 \| 0 \| 0 0 1 3 | Paley13, Kneser(6,2) |
| 0 0 1 2 3 \| 0 \| 0 0 0 2 | Kneser(7,2), Paley17 |
| 0 0 1 2 3 \| 0 \| 0 0 0 0 | Icosahedron |
| 0 0 0 1 2 \| 0 … (= K4) | K4, G(20,.2)#1, G(20,.3)#1,#2, G(30,.2) |
| 0 0 0 0 1 \| 0 … (= K5) | G(20,.5)#1,#2 |

- **Heawood: φ = φ(K2), as it must be.** C13 and C15 also equal K2 on B12, because every test has odd girth ≤ 9. The odd graphs K(7,3) and K(9,4) land exactly on C7 and C9. So B12 sees odd girth only up to 9.
- Once G ⊇ K4, the B12 profile depends only on α(K5,G) and α(K6,G). Random graphs therefore fall onto the K4 and K5 points.
- Among triangle-free targets of odd girth 5, the K-, C- and W5/Ico coordinates are all constant. B12 then tells them apart only through the (α(Pet,G), α(Grö,G)) pair, which takes 7 distinct values in this sample.
- Kneser(8,3), Chvátal/Circ(16;1,3,8) and M5/Clebsch have profiles that no n≤9 core has. These are the only new points B12 produces.

## 3. Stability (Spearman ρ between E_F and E_{F±T} over all pairs)

| targets | F | operation | #variants | min ρ | median ρ | most disruptive T |
|---|---|---|---|---|---|---|
| 85 | B12 | remove one | 12 | .973 | .999 | W5 |
| 85 | B12 | add one core | 73 | .980 | .995 | GQyurg |
| 85 | all | remove one | 85 | .9995 | .9999 | K4 |
| 1276 | B12 | remove one | 12 | .949 | .999 | W5 |
| 1276 | B12 | add one core | 150 (sample) | .968 | .994 | GCZTrW |
| 1276 | all | remove one | 150 (sample) | 1.000 | 1.000 | — |

The large family is extremely stable. The rankings are stable even for B12, but its zero set (which pairs are identified) is not: it changes with every added forced test.

## Takeaways for P/R/S

1. The effective dimension of about 1.2 to 1.5 is intrinsic: it holds for all families tested.
2. χ-balanced weights are the cheap fix that best aligns E with d*: Pearson .83 (vs .59 unweighted) on the 1276 cores.
3. E_F is a metric on cores only if F contains essentially every "near-critical" core. Formally, the minimum separating family is ≥ 253 for n ≤ 9 and grows with n. A finite basis therefore always gives a pseudometric.
4. For large graphs, B12 resolution is bounded by the tests' odd girth (≤ 9) and order (≤ 12). Adding C11, C13 and a χ=5 triangle-free test (M5) would be the next cheap step.
