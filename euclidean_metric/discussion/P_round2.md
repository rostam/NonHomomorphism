# Agent P — Round 2

## 1. A source-side profile that is constant on hom-classes
**Definition.**
 ψ_T(G) = max over probability weights w on E(G) of α_w(G,T),
where α_w(G,T) is the least w-weight of an edge set A with G − A → T. Equivalently, ψ_T(G) = 1 − s(T,G), the FJT separation. Equivalently again, ψ_T(G) = sup over (X,w) with X → G of α_w(X,T)/w(X).

**P15 (Theorem, the three forms agree).** "sup ≥ max" holds by taking X = G.
For "≤": take X → G via h and push w forward to w′ on G. Any partial map G → T pulls back along h, so mc_T(X,w) ≥ mc_T(G,w′), while w(X) = w′(G).
In the same way, any (X,w) can be restricted to its best G-colourable subgraph, which gives s(T,G) = inf over X → G. This is FJT Lemma 6.
- **This is a finite LP:** minimise t subject to Σ_w(preserved by f) ≤ t for all f : V(G) → V(T), with w a probability vector.
- By LP duality, ψ_T(G) = 1 − max over random maps F of min over e of Pr[F preserves e].
- With unweighted X the sup is the same: use D's random blow-ups. The value is attained at X = G when G is edge-transitive.

**P16 (Theorem: monotone, class-invariant, sees χ).**
- (a) G → G′ implies ψ(G) ≤ ψ(G′). The sup runs over a larger set. So ψ is constant on classes and **order-preserving**, while φ is order-reversing.
- (b) ψ_T(G) = 0 iff G → T. Hence **ψ_{K_k}(G) > 0 iff χ(G) > k**, and ψ_{C_{2k+1}}(G) = 0 iff χ_c(G) ≤ 2 + 1/k.
- (c) ψ(G⊔H) = **max**(ψ(G),ψ(H)) exactly. Write X as a union of components; the ratio for X is a mediant of the component ratios, and each connected component maps into G or into H.
  ψ(G×H) ≤ min(ψ(G),ψ(H)). Equality fails at the coordinate K_k for Shitov's pair. So **Hedetniemi is precisely "ψ_{K_k} is min-multiplicative"**.
- (d) ψ_T(G) ≥ α(G,T)/e(G) = φ_G(T), with equality if G is edge-transitive. So R and S's naive ψ is a lower bound, and it is exact for K_n, C_{2k+1}, Petersen and Kneser graphs.

**Closed forms.**
- ψ_{K_k}(K_n) = 1 − t(n,k)/C(n,2) (FJT Lemma 23).
- ψ_{K_k}(G) is sandwiched between the clique and chromatic values: ψ_{K_k}(K_{ω(G)}) ≤ ψ_{K_k}(G) ≤ ψ_{K_k}(K_{χ(G)}) ≤ 1/k.
- ψ_{K_2}(C_{2m+1}) = 1/(2m+1) and ψ_{K_2}(Petersen) = 1/5.
- ψ_{K_2}(G) = 1 − s(K₂,G), which is Šámal's χ_q via χ_q = 1/(1 − d(K₂,G)).
- Beyond these sandwiches, ψ_{K_k} has no closed form in χ: χ_f-type information enters.

**P17 (Theorem: (φ,ψ) is the better embedding).**
- Take G ↛ H. Then φ separates the pair if G ∈ 𝒯, and ψ separates it if H ∈ 𝒯. So (φ,ψ) needs only **one of the two members** in 𝒯, whichever it is.
- With 𝒯 = {K_k} alone, (φ,ψ) reads off **both ω and χ** exactly.
- In R's terms: φ encodes the up-set (what maps into G) and ψ the down-set (what G maps into).
- Cost: each ψ coordinate is an LP over |T|^{|G|} maps, but it needs only Aut(G)-orbit weights.

## 2. Checking S's claims
- **thm:lower_bound with ω(H): correct and strictly stronger.**
  - If G′ ⊆ G maps to H, then G′ contains no K_{ω(H)+1}, so e(G′) ≤ t(n,ω(H)) ≤ t(n,χ(H)). The bound is |G,H| ≥ e(G) − t(|V(G)|, ω(H)).
  - It is **tight for G = K_n and every H** (P4). The paper's χ-version is tight only when t(n,ω) = t(n,χ), for example when H is complete.
  - Example: |K_5,C_5| = 4. The paper's bound gives 10 − 8 = 2, while the ω-bound gives 10 − 6 = 4.
  - The proof in the paper (lines 207–218) is valid, just weak.
- **Hilbert link: correct.** Let p_G(T) = mc_G(T,w)/w(T), which is positive when G has an edge. Then
  log sup p_H/p_G + log sup p_G/p_H = −log s(G,H) − log s(H,G) = d_Hilbert(p_G,p_H).
  - It is a genuine metric (not just a projective one) because p_G(K₂) = 1 normalises every profile.
  - FJT's d = 1 − s(G,H)s(H,G) = 1 − e^{−d_Hilbert}. This is a concave, subadditive transform of d_Hilbert, so its triangle inequality is inherited.
  - Restricting to the coordinates in 𝔉 gives D's d_𝔉, which is still a pseudometric. So S is right.
  - Note: S's p_G is ψ read from the other side, since 1 − p_G(T) = φ_T(G) and s(T,G) = 1 − ψ_T(G). FJT is therefore a single object that has φ and ψ as its coordinate slices.
- **S's Prop P is false for ⊔.** "φ(G⊔H)_T = min for connected T" fails by P2: T is a chain of k triangles and k Grötzsch graphs joined by a bridge, with value ≤ 1 against ≥ k.
- **S's question 2 (connected T with φ(G×H)_T > max) has answer yes.** Take T = K₃ –bridge– Grötzsch. Then α(T,K₃) = α(T,Grö) = 1, and α(T,K₃×Grö) ≥ 2, using superadditivity over edge-disjoint subgraphs.

## 3. Why ≥ 253 tests are needed (Q)
**P18 (Theorem, critical-cover lemma).** Suppose H → G and G − e → H for **every** edge e (G is "H-critical"). Then α(S,H) = α(S,G) for every test S with mc_G(S) < e(G).
*Proof.* An optimal partial map S → G preserves fewer than e(G) edges, so it misses some edge e. Then S − A → G − e → H, which gives ≤. The reverse inequality ≥ comes from H → G.
So a test that separates G from H must hit **every** edge of G. Hence |V(S)| ≥ |V(G)| and e(S) ≥ e(G). If |V(S)| = |V(G)|, then S contains a spanning copy of G.

**Data check** (`P_forced.py`, n ≤ 9): 251 of the 253 forced pairs satisfy, in every case:
- H → G;
- α(G,H) = 1;
- G is H-critical;
- the pair is a **cover** of the core order: no core lies strictly between H and G.

The χ split is (4,4): 149, (5,5): 47, (4,5): 21, (3,4): 19, and so on.
The other 2 are covers with α = 2. These need the obvious generalisation: every optimal map misses some deletion set A with G − A → H.
**Hence forced tests = the tops of critical covers.** Among cores with at most n vertices, G is near-maximal in size, so it is the only test that hits all of its edges. The lower bound therefore grows with the number of critical covers.

These pairs have only **110 distinct lower ends** (K4: 21, K3: 19, …). Each pair is separated by ψ_H (ψ_H(G) ≥ 1/e(G) > 0 = ψ_H(H)). So the 253-forcing argument does not apply to (φ,ψ). This is concrete evidence for P17.
