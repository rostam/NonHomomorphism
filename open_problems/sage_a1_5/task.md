# Research task: the non-homomorphism parameter |G,H|

Definition: |G,H| = minimum number of edges to delete from G so that the remaining graph has a homomorphism to H. Equivalently, max over maps f:V(G)->V(H) of the number of G-edges sent to H-edges is |E(G)| - |G,H|. So |G,K_2| is the bipartization (max-cut complement) number and |G,K_k| = |E(G)| - maxcut_k(G).

Already KNOWN in our project (do not re-derive these; build on them):
- Monotonicity: H1->H2 implies |G,H1| >= |G,H2|; edge-injective G1->G2 implies |G1,H| <= |G2,H|.
- |K_n,K_m| = C(n,2) - t(n,m) (Turan). Lower bound |G,H| >= |E(G)| - t(|V(G)|, chi(H)).
- The symmetric m(G,H)=max(|G,H|,|H,G|) violates the triangle inequality (e.g. K7,K5,K3).
- Values: |Petersen,K2|=3, |Petersen,C5|=2, |Grotzsch,K3|=1, |Grotzsch,C5|=3, |K(6,2),K3|=3, |Icosahedron,K3|=3, |Icosahedron,C5|=10=|Icosahedron,K2|, |Dodecahedron,C5|=3, |Dodecahedron,K2|=6, |Paley13,K3|=5, |Paley13,C5|=13=|Paley13,K2|.
- Cubic girth>=5 graphs on <=22 vertices have |G,C5|/|E| <= 2/15 (Petersen worst); McGee and Coxeter graphs have |G,C5|=2.
- Quantitative Hedetniemi: |GxH,K| <= min(2|E(H)||G,K|, 2|E(G)||H,K|).

Goal: discover 3-5 NEW, interesting, precise statements about |G,H| and support each with tool computations, ideally exact formulas for infinite families (with a proof sketch when you can). Promising directions (pick what looks most fruitful):
1. Odd-cycle targets: closed formulas for |G, C_{2k+1}| for families G = K_n, power_cycle C_n^2, circulants, Kneser K(n,2), wheels, complete multipartite graphs. When does |G,C5| = |G,K2| (the "C5 gives no help" phenomenon)?
2. Mycielski chain: |M(k), K_{k-1}| for M(k) the k-chromatic Mycielski graph; |mycielskian G, H| vs |G,H|.
3. Line graphs / edge colouring: |L(G), K_Delta| measures "how far from class 1". Find formulas for L(K_n), L(Petersen), etc.
4. Random regular / G(n,p) statistics: how does |G,C5|/|E| compare with |G,K2|/|E| and |G,K3|/|E|?
5. Ratio / sub-additivity: triples with |G,K| > |G,H| + |H,K|·(something), or the ratio |G,C5|/|G,K2| as G varies.

Work in rounds: hypothesis -> batch computation -> refine. Finish with a section starting with "FINAL REPORT" listing each result as: statement, status (proved / verified for range X / conjectured), supporting data table, and why it is interesting.


## Data you already computed in an earlier session (exact values; do NOT recompute these)
| G | H | edges(G) | abs(G,H) |
|---|---|---|---|
| K10 | C3 | 45 | 12 |
| K10 | C5 | 45 | 20 |
| K10 | C7 | 45 | 20 |
| K10 | C9 | 45 | 20 |
| K5 | C3 | 10 | 2 |
| K5 | C5 | 10 | 4 |
| K5 | C7 | 10 | 4 |
| K5 | C9 | 10 | 4 |
| K6 | C3 | 15 | 3 |
| K6 | C5 | 15 | 6 |
| K6 | C7 | 15 | 6 |
| K6 | C9 | 15 | 6 |
| K7 | C3 | 21 | 5 |
| K7 | C5 | 21 | 9 |
| K7 | C7 | 21 | 9 |
| K7 | C9 | 21 | 9 |
| K8 | C3 | 28 | 7 |
| K8 | C5 | 28 | 12 |
| K8 | C7 | 28 | 12 |
| K8 | C9 | 28 | 12 |
| K9 | C3 | 36 | 9 |
| K9 | C5 | 36 | 16 |
| K9 | C7 | 36 | 16 |
| K9 | C9 | 36 | 16 |
| circulant 13 1 5 | C5 | 26 | 4 |
| circulant 13 1 5 | C7 | 26 | 6 |
| circulant 13 1 5 | C9 | 26 | 6 |
| complete_multipartite 2 2 2 2 | C5 | 24 | 8 |
| complete_multipartite 2 2 2 2 | C7 | 24 | 8 |
| complete_multipartite 3 3 3 | C5 | 27 | 9 |
| complete_multipartite 3 3 3 | C7 | 27 | 9 |
| kneser 6 2 | C5 | 45 | 15 |
| kneser 6 2 | C7 | 45 | 15 |
| power_cycle 10 2 | C3 | 20 | 1 |
| power_cycle 10 2 | C5 | 20 | 5 |
| power_cycle 10 2 | C9 | 20 | 6 |
| power_cycle 11 2 | C3 | 22 | 2 |
| power_cycle 11 2 | C5 | 22 | 6 |
| power_cycle 11 2 | C9 | 22 | 6 |
| power_cycle 12 2 | C3 | 24 | 0 |
| power_cycle 12 2 | C5 | 24 | 6 |
| power_cycle 12 2 | C9 | 24 | 6 |
| power_cycle 13 2 | C3 | 26 | 1 |
| power_cycle 13 2 | C5 | 26 | 7 |
| power_cycle 13 2 | C9 | 26 | 8 |
| power_cycle 14 2 | C3 | 28 | 2 |
| power_cycle 14 2 | C5 | 28 | 7 |
| power_cycle 14 2 | C9 | 28 | 8 |
| power_cycle 15 2 | C3 | 30 | 0 |
| power_cycle 15 2 | C5 | 30 | 8 |
| power_cycle 15 2 | C9 | 30 | 8 |
| power_cycle 8 2 | C3 | 16 | 2 |
| power_cycle 8 2 | C5 | 16 | 4 |
| power_cycle 8 2 | C9 | 16 | 4 |
| power_cycle 9 2 | C3 | 18 | 0 |
| power_cycle 9 2 | C5 | 18 | 5 |
| power_cycle 9 2 | C9 | 18 | 6 |
| wheel 10 | C3 | 18 | 1 |
| wheel 10 | C5 | 18 | 5 |
| wheel 10 | C7 | 18 | 5 |
| wheel 12 | C3 | 22 | 1 |
| wheel 12 | C5 | 22 | 6 |
| wheel 14 | C3 | 26 | 1 |
| wheel 14 | C5 | 26 | 7 |
| wheel 8 | C3 | 14 | 1 |
| wheel 8 | C5 | 14 | 4 |
| wheel 8 | C7 | 14 | 4 |

Start by stating 2-3 concrete patterns you see in this table, then test them on NEW cases (larger n, other targets such as K2, C11, K4, petersen, other families). Each reply must begin with a line 'Analysis:' (1-4 sentences) followed by the tool call.