# |G,H| exploration with Sage-A1.5 (2026-10-28)

Sage-A1.5 (InternScience, 35B MoE / ~3B active, Q4_K_M GGUF) was run locally with llama.cpp b11934
on CPU (i7-1355U, ~3–4 tok/s). It had one restricted tool, `nonhom_batch`, which computes |G,H| exactly with the
`parameter_fast_check` branch-and-bound solver (`graphs.py` parses a fixed graph-spec language, so the model never
runs code). Harness: `run_agent.py`, prompts: `task.md`, `system.md`; transcript: `sage_transcript.md`.

To reproduce the checks: `cd nhcli && cargo build --release`, then e.g. `python v2.py .` (needs `networkx`).

The run completed 6 turns (~130 solver queries) before llama-server was killed for low memory.
Sage produced the data and result 1; results 2–4 come from analysing its data and verifying further
(`v1.py`–`v4.py`). All values below are exact solver outputs unless marked.

## 1. Complete graphs: no triangle-free target helps (proved)

**|K_n, H| = C(n,2) − ⌊n²/4⌋ for every triangle-free H with an edge.**
Mantel: the kept graph maps to a triangle-free graph, so it is triangle-free. Verified n=5..12 for C5, C7, C9, C11, C13.
(Found by Sage. It is the special case G = K_{1,n} of result 2, since L(K_{1,n}) = K_n.)

## 2. Line graphs of regular graphs: the whole odd-cycle ladder collapses (proved)

**Theorem.** Let G be d-regular on n vertices, and suppose that 4 | d, or G is bipartite, or d is odd and G has a perfect
matching (e.g. every bridgeless cubic graph). Then for every triangle-free graph H with at least one edge,

    |L(G), H| = n · ⌊(d−1)²/4⌋.

In particular |L(G),C5| = |L(G),C7| = … = |L(G),K2|. For cubic G: |L(G),H| = n, i.e. exactly 1/3 of E(L(G)).

*Proof.* The d edges at each vertex v form a clique Q_v ≅ K_d in L(G), and these n cliques partition E(L(G)).
A homomorphic preimage of a triangle-free graph is triangle-free, so by Mantel each Q_v loses ≥ C(d,2) − ⌊d²/4⌋ = ⌊(d−1)²/4⌋ edges.
For the upper bound use K2 → H. A 2-colouring of V(L(G)) is a 2-edge-colouring of G, and it achieves the bound iff it is
balanced (⌊d/2⌋ vs ⌈d/2⌉) at every vertex. Such a colouring exists if 4 | d (Petersen's 2-factor theorem: split the d/2
2-factors evenly), if G is bipartite (König: group the d colour classes), and if d is odd with a perfect matching M.
In the last case G−M splits into (d−1)/2 2-factors; give colour 1 to M plus (d−1)/4 or (d−3)/4 of them, whichever is
an integer. ∎

| G | d | n | prediction | \|L(G),K2\| | \|L(G),C5\| | \|L(G),C7\| | \|L(G),K3\| |
|---|---|---|---|---|---|---|---|
| K4 | 3 | 4 | 4 | 4 | 4 | 4 | 0 |
| prism | 3 | 6 | 6 | 6 | 6 | 6 | 0 |
| K3,3 | 3 | 6 | 6 | 6 | 6 | 6 | 0 |
| cube Q3 | 3 | 8 | 8 | 8 | 8 | 8 | 0 |
| Petersen | 3 | 10 | 10 | 10 | 10 | 10 | **2** |
| Heawood / Möbius–Kantor / dodecahedron | 3 | 14/16/20 | 14/16/20 | 14/16/20 | (timeout) | | 0 |
| K5 | 4 | 5 | 10 | 10 | 10 | | |
| K4,4 | 4 | 8 | 16 | 16 | 16 | | |
| C8², C9² | 4 | 8, 9 | 16, 18 | 16, 18 | 16, 18 | | |
| K6 | 5 | 6 | 24 | 24 | 24 | | |
| K5,5 | 5 | 10 | 40 | 40 | (timeout) | | |

Contrast: |L(G),K3| = 0 iff G is 3-edge-colourable, and for Petersen it is 2. So among targets K3 → C5 → C7 → … → K2,
only K3 can tell snarks apart. Open question: is |L(G),K3| equal to the (vertex) resistance of a cubic graph G?

## 3. Squared cycles: an odd-cycle ladder that does not collapse (conjecture, verified n ≤ 22)

G = C_n² (circulant with jumps 1,2; 4-regular, n triangles). Write n = 4j + r.

- **|C_n², K3| = n mod 3** (verified 6 ≤ n ≤ 25).
- **|C_n², K2| = 2⌈n/4⌉** (verified 5 ≤ n ≤ 25).
- **|C_n², C_{2k+1}| = ⌈n/2⌉ if r ∈ {1,2} and k ≤ j; otherwise = 2⌈n/4⌉ = |C_n², K2|.**

So a longer odd cycle helps by exactly one edge, and only when n ≡ 1, 2 (mod 4) and the cycle is short enough (2k+1 ≤ 2j+1).
The lower bound ⌈n/2⌉ is proved: kept graphs are triangle-free, and each edge lies in ≤ 2 of the n triangles.
Heuristic for the threshold: deleting alternate rim edges leaves the jump-2 cycles, whose odd girth is ≈ 2j+1.

| n | K3 | C5 | C7 | C9 | C11 | K2 |
|---|---|---|---|---|---|---|
| 6 | 0 | 4 | 4 | 4 | 4 | 4 |
| 9 | 0 | **5** | 6 | 6 | 6 | 6 |
| 10 | 1 | **5** | 6 | 6 | 6 | 6 |
| 13 | 1 | **7** | **7** | 8 | 8 | 8 |
| 14 | 2 | **7** | **7** | 8 | 8 | 8 |
| 17 | 2 | **9** | **9** | **9** | 10 | 10 |
| 18 | 0 | **9** | **9** | **9** | 10 | 10 |
| 21 | 0 | **11** | **11** | **11** | ≤11 | 12 |
| 22 | 1 | **11** | **11** | **11** | **11** | 12 |
| 25 | 1 | **13** | | | ≤13 | 14 |

(n ≡ 0, 3 mod 4 rows: every odd cycle column equals the K2 column, e.g. n=12: 6 everywhere, n=15: 8 everywhere.)

## 4. Wheels (proved)

**|W_m, C_{2k+1}| = |W_m, K2| = ⌈m/2⌉** for rim length m ≥ 3 and all k ≥ 2. The m triangles each need a deletion and
a spoke covers ≤ 2 of them. Upper bound: alternate the rim colours and cut spokes to one class, plus one rim edge if m is odd.
Verified m = 3..20.

## 5. Generalized Petersen graphs GP(n,k)

Outer cycle u_0…u_{n−1}, spokes u_i v_i, inner edges v_i v_{i+k}; 2n vertices, 3n edges. GP(n,k) ≅ GP(n,l) when
kl ≡ ±1 (mod n). It is bipartite iff n is even and k is odd, and |GP(n,k),K3| = 0 always (Brooks).
Scripts: `gp2.py` (all k, 14 ≤ n ≤ 24, K2 and C5), `gp3.py` (K2, odd n ≤ 31), `gp5.py` (C5, k = 2,3,4, n ≤ 27),
`rot.py`; raw output in `data/`.

### 5a. Prisms (proved)

**|GP(n,1), C_{2k+1}| = 2 if n is odd and n < 2k+1, and 0 otherwise** (the same holds with K2 in place of C_{2k+1}, as the case k = ∞).
The outer and inner n-cycles are edge-disjoint, and an odd n-cycle maps to C_{2k+1} only if n ≥ 2k+1.
Deleting u_0u_1 and v_0v_1 leaves a bipartite ladder. If n ≥ 2k+1, lift f: C_n → C_{2k+1} by (i,a) ↦ f(i)+a.

### 5b. |GP(n,2), K2| = ⌈n/2⌉ + [n ≡ 2 (mod 4)] (lower bound proved; equality verified 5 ≤ n ≤ 24 and odd n ≤ 31)

*Lower bound.* The n 5-cycles C^i = u_i u_{i+1} u_{i+2} v_{i+2} v_i must each lose an edge. An outer edge lies on
exactly C^{i−1}, C^i, a spoke u_iv_i on exactly C^{i−2}, C^i, and an inner edge on one, so ≥ ⌈n/2⌉.
If n ≡ 2 (mod 4) and only n/2 edges are deleted, all of them must be outer edges or spokes. Then the inner rim (two cycles
of odd length n/2) is untouched, a contradiction. ∎

### 5c. Bipartization of GP(n,k) is achieved by "rotation" colourings (verified 168/168 cases, 5 ≤ n ≤ 31)

Place u_i at t·i and v_i at t·i + b on a circle of length 2n, and colour by half-circle. The minimum number of
monochromatic edges over t, b ∈ [0, 2n) equals the exact |GP(n,k),K2| in **every** computed case. So the
exponential search collapses to an O(n³) formula.

For odd n the simplest members (linear colourings) give the closed-form bound

    |GP(n,k), K2| ≤ min_t [ odd(t) + odd(t·k mod n) ],   odd(x) = whichever of x, n−x is odd,

which is exact in 97 of 111 odd-n cases. In the other 14 the truth is one less, and all have n ≡ 1 (mod 4)
(the k ≅ 2 class, plus GP(17,4), GP(25,4) ≅ GP(25,6)). With t = 1 this gives |GP(n,k),K2| ≤ k+1 for odd n and odd k, which is often sharp,
e.g. 4 for k = 3 and every odd n from 9 to 31.

### 5d. Maps to C5

- **GP(n,k) → C5 whenever 5 | n and k ≡ ±1 (mod 5)** (proved: u_i ↦ i, v_i ↦ i+1 mod 5). More generally,
  GP(n,k) → C_{2m+1} when (2m+1) | n and k ≡ ±1 (mod 2m+1).
- **|GP(n,4), C5| = (0, 1, 2, 1, 2)[n mod 5]** for all 13 ≤ n ≤ 27, and also n = 10, 11. The only small exception is GP(12,4) = 4.
  The zeros come from the bullet above. The upper bound for other residues presumably comes from patching that map, which is not proved.
- **|GP(n,3), C5| = 0 for all 14 ≤ n ≤ 27** (odd n is the content; even n is bipartite). For n = 7, 9, 11, 13 the
  values are 2, 3, 1, 1. (This may be related to known circular-chromatic-number results for GP(n,3).)
- GP(n,2) → C5 is genuinely costly. For n = 5…22 the values are
  2,2,2,2, 3,3,3,3, 4,3, 4,4,4,4, 5,5,5,5, and |GP(25,2),C5| = 5. This is roughly n/4.5 with no clean formula yet (note the dip at n = 14).
  The solver times out for n = 23, 24, 26, 27 (≤ 6).

| \|GP(n,k),K2\| / \|GP(n,k),C5\| | k=2 | k=3 | k=4 | k=5 |
|---|---|---|---|---|
| n=13 | 7 / 4 | 4 / 1 | 4 / 1 | — |
| n=15 | 8 / 4 | 4 / 0 | 6 / 0 | 6 / 5 |
| n=17 | 9 / 4 | 4 / 0 | 7 / 2 | 6 / 2 |
| n=19 | 10 / 5 | 4 / 0 | 6 / 2 | 6 / 2 |
| n=21 | 11 / 5 | 4 / 0 | 6 / 1 | 6 / 1 |
| n=23 | 12 / ≤6 | 4 / 0 | 8 / 1 | 6 / 1 |

## Other data from the run

- Mycielski: |M(k),K_{k−1}| = 1 for k = 3,4,5 (k-criticality). |M(5),K3| = 4, |M(5),C5| = 12, |M(4),C5| = 3.
- L(K_n) → K3: 5, 12, 21 for n = 5, 6, 7 (exact); L(K_n) → K4: 2, 6 for n = 5, 6.
- Ten random cubic graphs on 20 vertices: |G,C5| ∈ {0,1,3,4}; the max 4/30 = 2/15 equals the Petersen ratio.

## Notes on the model

With thinking on, Sage spent 2.3 h on its first turn and hit the token cap without calling the tool. With thinking off it
worked, but still had confusions (e.g. it asked whether G → C5 iff G is 3-colourable). It also sometimes re-sent
identical batches and needed de-duplication in the harness. Its useful contributions were choosing families to compute
and spotting result 1. On this hardware a GPU or the hosted API would be needed for longer sessions.
