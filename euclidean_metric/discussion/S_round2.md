# Agent S — Round 2: what to keep, what EFJT already has, and the final recommendation

I read P_round1, Q_round1 and R_round1. The paste-ready section is `discussion2/S_section.tex`. It test-compiles cleanly with stub labels and needs no extra packages.

**Sources.** FJT CSR'09 (arXiv:0802.0423) and Engström–Färnqvist–Jonsson–Thapper (EFJT), *DMTCS* 17:1 (2015) 33–66 (https://dmtcs.episciences.org/2118). I extracted the full text of both with pdftotext. Lemma and proposition numbers below are the journal (EFJT) numbering and were checked against that text.

## 1. Much of the profile theory is already in EFJT, in the language of separation

EFJT Definition 1.4: s(M,N) = inf over (G,w) of mc_M(G,w)/mc_N(G,w). Remark 1.5: M→N is not required.

| Our statement | EFJT equivalent | Status |
|---|---|---|
| P1(a) / Prop. I: G→H ⇒ φ(G) ≥ φ(H); class-invariance | Lemma 2.6 (H→N ⇒ s(M,N) ≤ s(M,H); proof: mc_H ≤ mc_N) and Prop. 2.8 (s is well defined on ≡-classes). FJT'09 Lemma 1 / Cor. 2–3. | **Known.** Cite it. |
| P1(b) order embedding (G ∈ 𝔉 ⇒ φ(G) ≥ φ(H) ⇒ G→H) | Implicit in FJT Lemma 4 (positivity of d). Not stated as an embedding. | One-line new observation. Keep. |
| P4: α(K_n,G) = C(n,2) − t(n,ω(G)) | **EFJT Prop. 2.4:** s(H,K_n) = e(T(n,r))/e(K_n) for ω(H) = r, stated with the hypothesis χ(H) ≤ n. The proof does not use that hypothesis. | **Known.** Cite it. The paper's Thm `thm:KnKm` is the special case H = K_m. |
| P6 / odd cycles | **EFJT Prop. 2.5:** s(K2,C_{2k+1}) = s(C_{2m+1},C_{2k+1}) = 2k/(2k+1) | **Known** for targets in the cycle chain. Our general-G version (decided by odd girth) is a trivial extension. |
| Edge-transitive coordinate φ_T(G) = 1 − s(G,T) | **EFJT Thm. 2.1:** s(M,N) = inf over Aut*(N)-invariant w of mc_M(N,w), and = mc_M(N, 1/e(N)) for edge-transitive N. Cor. 2.11: inf over all w on N. | **Known.** |
| P5: sup_T φ_T(G) = 1/ω(G) | Upper bound: Erdős' random r-partition (≥ (1−1/r)e edges) [check: Erdős 1965]. Limit: EFJT Prop. 2.4 as n→∞. EFJT Prop. 2.7 is a different lower bound. | Easy combination; not stated in EFJT. Keep it, short. |
| Hilbert-metric reading of d_FJT | Not in FJT/EFJT; they use d = 1 − s s^T. | **New, but definitional.** State it as a proposition with a one-line proof. |
| P8: bounded tests cannot see χ | Not in EFJT. | **New.** Keep it. |
| P2: not a lattice map | Not in EFJT. | New. Make it a remark with the K3 / Grötzsch example. This also **settles my round-1 "profile Hedetniemi" question negatively**, even for connected T (bridge version). Drop that question. |
| Load / γ Lipschitz bound (P13, my Prop. L) | Not in EFJT. | **New**, and it is the only bridge to the paper's γ. Keep. |
| Q: separating family ≥ 253 for n ≤ 9 | — | Computational remark plus an open question. |
| P10/P11 topology (image not closed, Mycielski chain, closure = countable graphs?) | — | Open question 2. P10's facts go in one sentence. |
| Tropical / (max,+) DP | BCLSV-style. Not in EFJT. | Remark only (computation). |

**Recommended statement list for the section (6 propositions):**
1. Monotonicity and order embedding (cite EFJT 2.6/2.8; the embedding is new). Includes the ‖φ‖₁ height-function corollary (R).
2. Clique and odd-cycle coordinates, reading off ω and odd girth (cite EFJT 2.4/2.5). Plus the **remark improving the paper's `thm:lower_bound` from χ(H) to ω(H)**. Example: |K5,C5| = 4, whereas the χ-bound gives 2.
3. Range: sup φ = 1/ω.
4. Blindness to χ (P8), with Q's ≥ 253 as a computational illustration.
5. Relation to FJT: the edge-transitive coordinate is 1 − s, and the FJT metric is the Hilbert metric on profiles.
6. Moving the target: |T,H| ≤ |T,G| + μ(f)|G,H|, the link to γ.

The lattice failure, the tropical DP and the topology facts become remarks or open questions. Dropped: "profile Hedetniemi" (answered by P2), graphon extension (too far afield), and ML kernel claims (see §3).

## 2. The source-side profile ψ: it is exactly EFJT's separation, read from the other side

P's ψ(G)_T = sup over X→G of α(X,T)/e(X).
- With weighted X, it is **exactly 1 − s(T,G)**. Any (X,w) with X→G has mc_G(X,w) = ‖w‖, so 1 − ψ = inf mc_T(X,w)/‖w‖ ≥ s(T,G). EFJT Thm 2.1 / Cor 2.11 shows the inf over all (X,w) is attained at X = G (which maps to G) with Aut-invariant weights. So
  **ψ^w(G)_T = 1 − s(T,G) = max over w ∈ Ŵ(G) of (1 − mc_T(G,w))**, by EFJT Definition 1.4 + Theorem 2.1.
- Class-invariance in G (and in T) is **EFJT Prop. 2.8**. Monotonicity is Lemma 2.6.
- **EFJT Prop. 5.4:** χ_T(G) = 1/s(T,G), where χ_T(G) is the fractional covering number of G by T-cuts (EFJT Def. 5.2, LP (11)). Hence **ψ^w(G)_T = 1 − 1/χ_T(G)**.
  - For T = K2, χ_{K2} is Šámal's cubical chromatic number, so ψ_{K2}(G) = 1 − 1/χ_q(G).
  - **EFJT Cor. 5.9:** s(K2,G) takes every rational value in (1/2, 1].
- Computation: by Thm 2.1, a coordinate is a small LP over the Aut*(G)-orbits of edges. For edge-transitive G, ψ(G)_T = |G,T|/e(G) exactly.
- **Unweighted version** (sup over simple X→G only). We get ψ ≤ 1 − s(T,G), with equality for edge-transitive G (X = G).
  - Every X→G is a subgraph of a blow-up of G, but blow-ups give only product weights.
  - Equality in general needs D's random-bipartite-block (graphon) argument. Neither FJT nor EFJT states it. This is open question 3 in the section.
- **Recommendation to P.** Define ψ with weights, ψ(G)_T := 1 − s(T,G), cite EFJT, and do **not** present ψ as new.
  - What is new is the pairing (φ, ψ): the target-side column and the source-side row of the separation matrix.
  - Also new is the observation that ψ_{K_k}(G) = 0 ⇔ G → K_k, so ψ sees χ (R's point) while φ sees ω.
  - In this language, d_FJT(G,H) = 1 − (1 − ψ_H(G))(1 − ψ_G(H)) for edge-transitive G,H.

## 3. Final recommendation for the user

**What the profile is good for:**
- **A unifying picture.** One embedding G ↦ φ(G) carries three distances: the ℓ∞ test-graph metric, the Euclidean E, and the FJT metric (Hilbert projective metric).
  - This replaces the failed "is m a metric?" question (`q:metric`) with a clean, true statement: a metric on hom-classes, with an approximation-theoretic meaning through FJT/EFJT Lemma 1.6.
- **Exact readouts.** ω and odd girth come from single coordinates. ‖φ‖₁ is a strict height function of the hom order: R found 0 violations over 2966 comparable pairs.
- **Picturing the hom order.** PCA/MDS figures, clusters that are up-sets, and the empty region between K3 and K4 (R) are good figure material for the computational section.
- **A bridge to γ.** The Lipschitz bound makes the concentration parameter the sensitivity of the profile. This gives the paper's two parameters one storyline.
- **A free improvement to an existing theorem.** |G,H| ≥ e(G) − t(v(G), ω(H)).

**What it is not good for:**
- **χ, χ_f, bipartiteness.** None is visible to any bounded test family (P8). About 91% of the variance is the ω-class (R), and the effective dimension is about 1.2–1.5 (Q).
- **A compact invariant.** Separating the n ≤ 9 cores needs at least 253 tests (Q). Any finite basis gives only a pseudometric.
- **Lattice operations.** φ is not a lattice homomorphism (P2).
- **Graph-ML features on large real graphs.** Targets with ω ≥ 4 swallow every small test. The source side ψ (Max-Cut-type ratios) is the useful feature vector, and ψ is EFJT's separation.
- **Novelty claims.** Clique and odd-cycle values, monotonicity and class invariance are in EFJT. Present the profile as a repackaging plus four new observations: embedding, blindness, the Hilbert form and the γ-Lipschitz bound.

**Three best open questions:**
1. **Separating-family growth σ(n).** We know 253 ≤ σ(9) ≤ 311. Which cores are forced? Is σ(n) of the order of the number of cores?
2. **Closure of the profile space.** Is it exactly the set of profiles of countable graphs (P11)? Is the space of hom-classes totally bounded under ℓ∞ (P12)?
3. **Unweighted equals weighted separation.** Is sup over simple X→G of |X,T|/e(X) = 1 − s(T,G)? A yes would make FJT and ψ weight-free and tie |·,·| directly to EFJT's fractional T-cut covers.

## 4. Citations used (verified unless marked)
- FJT, CSR 2009, LNCS 5675:92–104, arXiv:0802.0423 (Lemmas 1, 4, 8, 18, 23 in that numbering).
- EFJT, DMTCS 17:1 (2015) 33–66, https://dmtcs.episciences.org/2118: Def. 1.4, Lemma 1.6, Thm 2.1, Prop. 2.4, Prop. 2.5, Lemma 2.6, Prop. 2.7, Prop. 2.8, Cor. 2.11, Prop. 5.4, Cor. 5.8–5.9.
- Šámal, DMTCS 17:2 (2015), arXiv:0911.2589.
- Langberg–Rabani–Swamy, APPROX 2006, LNCS 4110:176–187.
- Dell–Grohe–Rattan, ICALP 2018.
- Erdős 1965 random-partition bound [check].
- Lovász 1967 [check].
