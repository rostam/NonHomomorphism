# Agent P (Theorist) — Round 1: the α-profile φ

Notation. φ_T(G) = α(T,G)/e(T) = 1 − mc_G(T)/e(T), where mc_G(T) is the largest number of edges of T that some vertex map V(T)→V(G) sends onto edges. G is the **target**. E₂ = weighted ℓ₂, E_∞ = sup_T |Δφ_T|, δ = test-graph metric, δ_w = FJT max-metric (A7), d_n = max(α(G,H)/e(G), α(H,G)/e(H)).
**Standing fact (F).** φ_T takes values in (1/e(T))ℤ ∩ [0,1]. So for a finite 𝒯 the image is finite. For an infinite 𝒯, convergence in the product topology means every coordinate is eventually constant.
Script: `discussion2/P_check.py`. On both the 85 cores and the 1276 cores (n ≤ 9) it finds 0 failures for P1 (with 𝒯 = all cores), P4 and P5.

## 1. Order structure
**P1 (Theorem, order embedding).**
- (a) G→H implies φ(G) ≥ φ(H) coordinatewise. *Proof:* compose any map T→G with G→H. No preserved edge is lost.
- (b) If 𝒯 contains a graph hom-equivalent to G, then φ(G) ≥ φ(H) implies G→H. *Proof:* φ_G(H) ≤ φ_G(G) = 0.
- So if 𝒯 contains every connected core, G→H ⇔ φ(G) ≥ φ(H). The homomorphism order embeds **anti-isomorphically** into (ℝ^𝒯, ≤). Connected cores are enough: apply (b) to each component.
- (c) Having only H ∈ 𝒯 is not enough. Take 𝒯 = {K₂}: then φ(K₃) = φ(K₂) = 0, but K₃ ↛ K₂.

**P2 (Theorem + counterexamples, lattice operations).** In the hom order, G⊔H is the join and G×H is the meet. Because φ reverses the order:
- φ(G⊔H) ≤ min(φ(G),φ(H)) and φ(G×H) ≥ max(φ(G),φ(H)).
- Both inequalities can be strict, so **φ is not a lattice map**.
- Exact formula for the union: α(T,G⊔H) = min over partitions (A,B) of V(T) of [e(A,B) + α(T[A],G) + α(T[B],H)].
- *Strict for ⊔:* let G = K₃ and H = Grötzsch (an incomparable pair). Let T be k triangles in a chain, joined by one bridge to a chain of k Grötzsch copies, with chain bridges chosen so they can be preserved. Then α(T,G⊔H) ≤ 1, while α(T,K₃) ≥ k and α(T,Grö) ≥ k. (Here α is superadditive over edge-disjoint subgraphs, and Grötzsch is 4-critical and triangle-free.)
- *Strict for ×:* let T = K₃ ∪ Grötzsch, optionally joined by a bridge. Then α(T,K₃) = α(T,Grö) = 1. But K₃×Grö is triangle-free and is not reached by Grötzsch (Grö ↛ K₃), so α(T, K₃×Grö) ≥ 2.
- Hedetniemi in this language: the set U_n = {x ≥ φ(K_n)} is exactly {χ ≤ n} (by P1). U_n is closed under coordinatewise max of the factor profiles but not under the product, by Shitov.

**P3 (Theorem, the meet and join are exact on clique coordinates).** See P4: φ_{K_k} depends only on ω, and ω(G⊔H) = max(ω(G),ω(H)), ω(G×H) = min(ω(G),ω(H)). So φ_{K_k}(G⊔H) = min and φ_{K_k}(G×H) = max.

## 2. Which parameters φ recovers
**P4 (Theorem, clique coordinates).** α(K_k,G) = C(k,2) − t(k, min(k,ω(G))), where t is the Turán number.
*Proof:* the preserved edges form a k-vertex graph that maps to G. It is therefore K_{ω+1}-free, so Turán's theorem applies. A balanced map onto an ω-clique attains the bound.
- Hence φ_{K_k}(G) = 0 iff ω(G) ≥ k, and φ_{K_k}(G) is strictly decreasing in ω for ω < k.
- So φ_{K_k} for any single k > ω determines ω.

**P5 (Theorem, the sup-norm is 1/ω).** For every T, φ_T(G) ≤ φ_T(K_{ω(G)}) ≤ 1/ω(G). The second step uses a uniformly random ω-colouring. Also φ_{K_k}(G) = (k−ω)/(ω(k−1)) + O(1/k) → 1/ω.
So **sup_T φ_T(G) = 1/ω(G)** (cliques never attain it). Consequently E_∞(G,H) ≥ |1/ω(G) − 1/ω(H)|.

**P6 (Theorem, odd girth).** If G has an edge, then φ_{C_{2k+1}}(G) ∈ {0, 1/(2k+1)}, and it is 0 iff og(G) ≤ 2k+1. So og(G) = min{2k+1 : φ_{C_{2k+1}}(G) = 0}. Also φ_T(K₂) = 1 − b(T), where b is the bipartite (max-cut) density, and φ(K₂) is the maximum of φ over all non-edgeless G.

**P7 (Theorem, χ and χ_f are sandwiched).**
- φ(K_{χ(G)}) ≤ φ(G) ≤ φ(K_{ω(G)}). Also φ(G) ≥ φ(K(a,b)) when χ_f = a/b, via the Kneser graph.
- χ(G) = min{n : φ(G) ≥ φ(K_n)} when G ∈ 𝒯.

**P8 (Counterexample: no finite family sees χ).** Let 𝒯 be any family of graphs with at most m vertices. If og(G) > m, then **φ_𝒯(G) = φ_𝒯(K₂)**. *Proof:* the image of the preserved edges has at most m vertices, so it is bipartite and factors through K₂ ⊆ G.
- So χ, χ_f and even bipartiteness are invisible to every finite or bounded-order 𝒯.
- With summable weights, E₂(G,K₂)² ≤ Σ_{|T|>m} w_T → 0 as og(G) → ∞, for any χ.

**P9 (Theorem, Lipschitz relations).**
- (i) d_n(G,H) ≤ E_∞(G,H) ≤ δ(G,H) = δ_w(G,H) ≤ 1. The first inequality needs G,H ∈ 𝒯.
  - Proof of the upper bound: A1 gives φ_T(H) − φ_T(G) ≤ (1−s(H,G))(1−φ_T(G)).
  - Equality E_∞ = δ holds when 𝒯 = all graphs (D: unweighted inf = weighted s).
- (ii) Raw ℓ∞ dominates dist, but on any infinite 𝒯 that is closed under disjoint copies it is +∞ for distinct classes, since α(mG,H) = m·α(G,H). Only normalised coordinates make sense.
- (iii) E_∞ ≤ 1 ≤ d* trivially, and the bound cannot be reversed: d*(K_n,K_m) = |n−m| while E_∞ ≤ 1. More sharply, E_∞(K_n,K_m) ≤ 1/min(n,m), so (K_n) is **δ-Cauchy**. E is therefore a "high-χ compressing" metric: large χ is far in d* but close in E.
- (iv) E₂ ≤ (Σw)^{1/2} E_∞. The reverse fails: take G_k of girth > k with b(G_k) → 1/2. Then E₂(G_k,K₂) → 0, while δ(G_k,K₂) ≥ φ_{G_k}(K₂) → 1/2.

## 3. Infinite families
**P10 (Theorem).** Let 𝒯 ⊇ all connected cores, with w_T > 0 and Σ w_T < ∞.
- E₂ is a **metric on hom-classes** (by P1).
- Weighted ℓ₂ induces the product topology on [0,1]^𝒯, which is compact. So the space is **totally bounded and separable** (it is countable), but **not complete**.
- **Image not closed:** φ(K_n) → 0. The zero vector would mean "T→G for all T", which no finite G satisfies.
- **Mycielski chain:** M_k ⊂ M_{k+1} has φ(M_k) ↓ ψ with ψ ∉ image. If ψ = φ(G), then ψ_G = 0. By (F), φ_G(M_j) = 0 for large j, so G → M_j. Also ψ_{M_{j+1}} = 0, so M_{j+1} → G → M_j, which contradicts χ(M_{j+1}) > χ(M_j).
- **Not convex:** by (F) each coordinate of the closure lies in a finite set, so the closure is totally disconnected (Cantor-like).
- **Limits:** C_{2k+1} → K₂, and more generally og → ∞ gives → φ(K₂) for any χ (P8). Non-isolated points therefore exist.

**P11 (Conjecture).** cl φ(cores) = {φ(X) : X a countable graph}, where φ_T(X) uses maps into the infinite X. Monotone chains give φ(⋃G_k). Proving it for general sequences needs a compactness or ultraproduct argument.

**P12 (Question).** Is (cores, δ) totally bounded? (K_n) and (C_{2k+1}) are δ-Cauchy. An infinite δ-ε-separated family would need s(H_i,H_j) ≤ 1−ε for all i ≠ j.

## 4. Deleting an edge of the target
**P13 (Theorem).** φ(G−e) ≥ φ(G), and
 α(T,G−e) − α(T,G) ≤ min over optimal f of m_e(f) ≤ e(T) − α(T,G),
where m_e(f) is the number of preserved T-edges that f places on e.
- If T → G, then α(T,G−e) ≤ γ(T,G), the concentration parameter, for every e.
- If G is edge-transitive, average over Aut(G): φ_T(G−e) − φ_T(G) ≤ (1−φ_T(G))/e(G) ≤ 1/e(G).

**P14 (Counterexample: no uniform continuity).** Let G = K₃ with a long path attached, and let e be a triangle edge. Then φ_{K₃} jumps from 0 to 1/3, however large e(G) is. For G = K₂ the jump is b(T) ≥ 1/2 in every coordinate. So φ is edge-continuous only in hom-class-sensitive ways. The bound in P13 is the right local statement.
