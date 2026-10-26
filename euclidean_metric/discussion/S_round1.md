# Agent S — Round 1: literature and paper placement for the α-profile

Notation used below:
- α(T,G) = |T,G|, the fewest edges to delete from T so that T maps to G.
- mc_G(T) = e(T) − α(T,G), the size of a largest G-colourable subgraph of T. This is the Max G-Col optimum.
- φ(G)_T = α(T,G)/e(T) ∈ [0,1], and p_G(T) = 1 − φ(G)_T = mc_G(T)/e(T).
- E_w(G,H) = (Σ_T w_T (φ(G)_T − φ(H)_T)²)^{1/2}.

Citation tags:
- **[V]** = checked on the web in this round, or in D_round2.
- **[M]** = from memory, not checked; check before putting it in the paper.

Brute-force sanity checks are in `scratchpad/s_lit/chk2.py`.

---

## 1. Prior work: is the "α-profile" already known?

**Verdict.** I found **no** paper that defines a vector of normalised max-H-colourable-subgraph values over a family of test graphs, with the target varying, and uses it as an embedding or Euclidean distance. Searches covered:
- "max H-colourable subgraph profile/vector"
- "edge-deletion homomorphism profile"
- "approximate homomorphism indistinguishability"
- "tropical/max-plus homomorphism numbers"
- "homomorphism distance fraction of edges preserved"

The ingredients are all classical, though. Each closest relative below matches one ingredient, so the paper should present φ as a **synthesis** and claim novelty only for that synthesis.

| Line of work | Object | Relation to φ |
|---|---|---|
| **Lovász 1967** [M: "Operations with structures", Acta Math. Acad. Sci. Hungar. 18 (1967) 321–328]; Lovász, *Large Networks and Graph Limits*, AMS Colloq. Publ. 60 (2012) [M] | hom(F,G) for all F determines G up to isomorphism | φ is the **(max,+) tropicalisation** of the left homomorphism vector (§2, Prop. T). Its zero set {T : φ(G)_T = 0} is the hom-existence profile, which determines the hom-class. |
| **Dell–Grohe–Rattan**, "Lovász meets Weisfeiler and Leman", ICALP 2018, LIPIcs 107, 40:1–40:14, doi:10.4230/LIPIcs.ICALP.2018.40, arXiv:1802.08876 [V] https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2018.40 | hom vectors restricted to trees / treewidth ≤ k ⇔ colour refinement / k-WL | A model for "restricted test family ⇒ known equivalence". The analogue for φ is open: which equivalence does φ restricted to a family 𝔉 induce (Q4)? |
| **Grohe**, "word2vec, node2vec, graph2vec, X2vec", PODS 2020, doi:10.1145/3375395.3387641, arXiv:2003.12590 [V] | hom vectors as graph embeddings, "homomorphism indistinguishability" | The ML framing. φ is a new "X2vec" with an optimisation flavour in place of counting. |
| **NT & Maehara**, "Graph Homomorphism Convolution", ICML 2020, PMLR 119:7306–7316, arXiv:2005.01214 [V] https://proceedings.mlr.press/v119/nguyen20c.html | hom-count features (bounded-treewidth F) with a universality theorem | Closest ML precedent. A φ-kernel would sit beside it (§3). |
| **BCLSV II**, "Convergent sequences of dense graphs II. Multiway cuts and statistical physics", Ann. of Math. 176 (2012) 151–219, doi:10.4007/annals.2012.176.1.2 [V] | ground-state energies Ê(G,J) = max over q-partitions of Σ J_ij·(edge density between parts), and their cut-continuity ("right convergence ⇔ left convergence") | With J = A_H, Ê(T,A_H)·n² = mc_H(T), so **every coordinate of φ is a ground-state energy of the test T in the "model" G**. The roles are reversed from BCLSV: there the model is fixed and the large graph varies. Here the test varies and the model is the object. Cut-continuity lets φ(G) be evaluated on graphons (Prop. G). |
| **Färnqvist–Jonsson–Thapper (FJT)**, "Approximability distance in the space of H-colourability problems", CSR 2009, LNCS 5675:92–104, doi:10.1007/978-3-642-03351-3_11, arXiv:0802.0423 [V] | s(M,N) = inf_{(G,w)} mc_M(G,w)/mc_N(G,w); metric d = 1 − s(M,N)s(N,M) on hom-classes | **FJT is a distance on the same profile.** On edge-transitive tests, 1 − φ(G)_T = s(G,T) (FJT Lemma 8). The additive FJT distance is exactly **Hilbert's projective metric** on the profiles p_G (Prop. H). |
| **Engström–Färnqvist–Jonsson–Thapper**, DMTCS 17:1 (2015) 33–66 [V via D]; arXiv:0904.4600 [V] | s on circular cliques K_{p/q}, links to Šámal's cubical colouring | Source of more closed forms (φ(K_{p/q})_T). |
| **Šámal**, "Cubical coloring — fractional covering by cuts and semidefinite programming", DMTCS 17:2 (2015), arXiv:0911.2589 [V] https://dmtcs.episciences.org/2134 | χ_q(G) from fractional cut covers; FJT state χ_q(H) = 1/(1−d(K2,H)) [V, FJT text] | Gives a "bipartite-density" family of invariants of the same kind. |
| **Langberg–Rabani–Swamy**, "Approximation algorithms for graph homomorphism problems", APPROX 2006, LNCS 4110:176–187, doi:10.1007/11830924_18 [V] | Maximum Graph Homomorphism (MGH): max edges preserved by a map G→H; a (1/2+Ω(1/(|H| log|H|)))-approximation | Proves that **mc_H(T) is the MGH objective**. Cite it for complexity and approximation of the coordinates. |
| **Nakajima–Živný**, "A dichotomy for maximum PCSPs on graphs", arXiv:2406.20069 [V] | MaxPCSP(G,H): given ρ-fraction G-satisfiable, find ρ-fraction H-satisfying | Promise version of comparing two profile coordinates, p_G(T) vs p_H(T). |
| **Edit distance to hereditary properties**: Alon–Stav, "What is the furthest graph from a hereditary property?" RSA 33 (2008) [M for details]; Axenovich–Kézdy–Martin JGT 58 (2008) [V via D]; Balogh–Martin, "Edit distance and its computation", EJC 15 (2008) R20 [V] https://www.combinatorics.org/ojs/index.php/eljc/article/download/v15i1r20/pdf | ed_𝒫(G) and ed_𝒫(p) | 𝒫_H = {T : T → H} is a **monotone** property, so the edit distance to it is pure deletion. Hence **α(T,H) = ed_{𝒫_H}(T)**, and sup over n-vertex T of α(T,H)/C(n,2) is the Alon–Stav max-distance of 𝒫_H. |
| **Hell–Nešetřil**, *Graphs and Homomorphisms*, OUP 2004 [V via paper]; Welzl, TCS 17 (1982) 29–41 [V via D] | the homomorphism order is a distributive lattice, dense above K2 | φ is an order-embedding of this lattice into ([0,1]^𝔉, ≥) (Prop. O). |
| **Hilbert projective metric**: Hilbert, Math. Ann. 46 (1895) 91–96 [M]; Thompson, Proc. AMS 14 (1963) 438–443 [M]; Lemmens–Nussbaum, *Nonlinear Perron–Frobenius Theory*, CUP 2012 [M] | d_H(x,y) = log max_i(x_i/y_i) + log max_j(y_j/x_j) on positive cones | Identifies FJT's additive metric (Prop. H). |

**Recommended framing sentence.** "The α-profile is the max-plus analogue of Lovász's homomorphism vector. Its coordinates are Max-G-Col values (Langberg–Rabani–Swamy) or ground-state energies (BCLSV) of the test graphs. The Färnqvist–Jonsson–Thapper metric is the Hilbert projective metric on these profiles, and E is the Euclidean counterpart."

---

## 2. Structural facts and closed forms

### Basic propositions. Proofs are short; they are suitable for the paper.

**Prop. I (well defined on hom-classes; monotone).**
- If G → H, then φ(G)_T ≥ φ(H)_T for every T. Any T − S → G composes to T − S → H.
- Hence G ↔ H implies φ(G) = φ(H).
- *Contrast:* the source side is **not** class-invariant: |2K4,K3| = 2 ≠ |K4,K3| (D_round2).

**Prop. O (order embedding).** Suppose 𝔉 contains the cores of G and H. Then G → H ⇔ φ(H) ≤ φ(G) coordinatewise.
- *Proof of ⇐.* φ(G)_{core G} = 0, so φ(H)_{core G} = 0, i.e. core G → H.
- *Corollary:* E_w (with all w_T > 0) and δ_𝔉 = ‖φ(G)−φ(H)‖_∞ are **genuine metrics on the hom-classes of 𝔉-cores**. This is positivity; symmetry and the triangle inequality come free from the norm.
- *Supporting fact:* the zero pattern of φ(G) is the "Lovász hom-existence vector" {T : T → G}.

**Prop. T (tropicalisation of hom numbers).** Let W_β(G) be the looped complete weighted graph on V(G), with weight e^β on the edges of G and 1 on non-edges and loops. Then

  mc_G(T) = lim_{β→∞} β^{-1} log hom(T, W_β(G)), with 0 ≤ β^{-1}log hom − mc_G(T) ≤ v(T) log v(G)/β.

*Proof.* hom(T,W_β) = Σ_{f: V(T)→V(G)} exp(β·#edges preserved by f). Bound this between the largest term and V(G)^{V(T)} times the largest term.
- *Algorithmic corollary.* The tree-decomposition DP for hom(T,·) works over any commutative semiring. Run it in (max,+) instead of (+,×) to compute mc_G(T) in O(v(T)·v(G)^{tw(T)+1}). This gives a **polynomial-time profile on any bounded-treewidth test family**, exactly as in NT–Maehara and Dell–Grohe–Rattan.

**Prop. F (FJT coordinates).**
- (a) If T is edge-transitive, then φ(G)_T = 1 − s(G,T). This is FJT Lemma 8: s(M,N) = mc_M(N, 1/e(N)) for edge-transitive N.
- (b) In general, s(G,H) = inf_{(T,w)} p_G(T,w)/p_H(T,w). So s is the inf of a coordinate ratio of (weighted) profiles.

**Prop. H (FJT = Hilbert metric on profiles).** Let p_G = 1 − φ(G), indexed by all edge-weighted test graphs. Then

  −log s(G,H) − log s(H,G) = log sup_T p_H(T)/p_G(T) + log sup_T p_G(T)/p_H(T) = d_Hilbert(p_G, p_H).

- max(−log s(G,H), −log s(H,G)) is the Thompson metric.
- Hilbert's metric is projective (zero on proportional vectors). However, p_G(K2) = 1 for every G with an edge, so proportional means equal. The metric property therefore follows from Prop. O, independently of FJT's proof.
- **Consequence for the paper:** δ_𝔉 (ℓ∞), E (ℓ2) and FJT (Hilbert) are three norms/metrics on **one** embedding, G ↦ φ(G). The FJT triangle inequality is the triangle inequality of d_Hilbert.
- *Finite-family version:* d_𝔉 from D_round2 is the Hilbert metric restricted to the coordinates in 𝔉. This explains why it had 0 triangle violations.

**Prop. L (Lipschitz control by the concentration γ).** Let f: T − S → G be optimal, with load μ(f) = max over e ∈ E(G) of |f^{-1}(e)|. Then

  α(T,H) ≤ α(T,G) + μ(f)·α(G,H), so φ(H)_T − φ(G)_T ≤ μ(f)·α(G,H)/e(T).

*Proof.* Delete S, then delete the f-preimages of an optimal S' ⊆ E(G).
- This **links the user's γ parameter to the profile**: γ(T,G), or more precisely the min load over optimal maps, is the local Lipschitz constant of φ under moving the target.
- It is D's load-weighted triangle inequality, now read coordinatewise.

**Prop. P (products and unions of targets).**
- For connected T: φ(G ⊔ H)_T = min(φ(G)_T, φ(H)_T).
- For every T: max(φ(G)_T, φ(H)_T) ≤ φ(G×H)_T ≤ φ(G)_T + φ(H)_T. This uses T' → G×H ⇔ T' → G and T' → H, and deleting S_G ∪ S_H.
- Equality with max holds on cliques and odd cycles, because ω(G×H) = min ω and og(G×H) = max og.
- It fails in general. T = K3 ⊔ Grötzsch, G = K3, H = Grötzsch gives α(T,G×H) = 2 > max(α(T,G), α(T,H)) = 1. Checked: α(Grötzsch,K3) = 1 by brute force.
- **Q:** Is there a *connected* T with φ(G×H)_T > max(φ(G)_T, φ(H)_T)? This is a "profile Hedetniemi" question. Hedetniemi itself (Shitov 2019, Ann. Math. 190 [M]) lives on the *source* side, so it is not this.

### Closed-form coordinates

Recall φ(G)_T = α(T,G)/e(T). Write t(n,r) for the Turán number, ω for clique number, og for odd girth, and T(n,r) for the Turán graph.

| Test T | Target G | α(T,G) | φ(G)_T | Source / status |
|---|---|---|---|---|
| K_n | **any** G with ω(G) = r | C(n,2) − t(n,r) | 1 − t(n,r)/C(n,2) → 1/r | **New, slightly stronger than the paper.** A subgraph mapping to G is K_{r+1}-free, and blowing up a max clique attains t(n,r). Turán gives the rest. The paper's Thm `thm:KnKm` is the case G = K_m; FJT Lemma 23 gives s(K_r,K_n) = t(n,r)/C(n,2). Brute-force checks: K5→C5: 4, K4→C5: 2, K5→Petersen: 4, K6→Grötzsch: 6. ✓ |
| K_n | C_{2k+1}, k ≥ 2 | C(n,2) − ⌊n²/4⌋ = ⌊(n−1)²/4⌋ | → 1/2 | the row above with r = 2 |
| C_{2k+1} | G non-bipartite, og(G) ≤ 2k+1 | 0 | 0 | C_{2k+1} → C_{og} ⊆ G |
| C_{2k+1} | G bipartite with ≥ 1 edge, or og(G) > 2k+1 | 1 | 1/(2k+1) | path P_{2k+1} → K2. FJT Lemma 18: s(K2,C_k) = s(C_m,C_k) = (k−1)/k for odd k < m. Brute force: C5→C7 gives 1. ✓ |
| C_{2k} or any bipartite T | G with ≥ 1 edge | 0 | 0 | so **bipartite tests carry no information** |
| Petersen P | K2 | 3 | 1/5 | b(P) = 4/5 (Bondy–Locke JGT 10 (1986) [V via D]; FJT p. 900 [V]). Paper `obs:PK2`. |
| Petersen P | C5 | 2 | 2/15 | brute force (chk2.py). P ↛ C5 since χ_c(P) = 3 [M] |
| Petersen P | G ⊇ K3 | 0 | 0 | χ(P) = 3 |
| Dodecahedron | K2 | 6 | 1/5 | brute force; Bondy–Locke extremal [M] |
| Grötzsch (Mycielski of C5) | K3 / C5 | 1 / 3 | 1/20 / 3/20 | brute force |
| Kneser K(2k+1,k) (edge-transitive, odd girth 2k+1) | K2 | ≥ C(2k+1,k)(k+1)/(2(2k+1)) | ≥ 1/(2k+1) | D_round2 averaging argument |
| edge-transitive T | any G | e(T)(1 − s(G,T)) | 1 − s(G,T) | FJT Lemma 8. Imports every FJT/EFJT computation, e.g. wheels: s(K3,W_n) = (2k−3)/(2k−2) for even n [V, FJT Example 9; check indexing] |
| G(n,p), n → ∞ (dense random) | any G with ω(G) = r | — | → 1/r a.s. | Motzkin–Straus (Canad. J. Math. 17 (1965) 533–540 [M]) + quasirandomness. **Dense random tests see only ω.** |
| G(n,c/n) (sparse random) | K2 | — | → 1/2 − P*/√c + o(1/√c) | Dembo–Montanari–Sen, Ann. Probab. 45 (2017) [M]. **Sparse tests see more than ω.** |

**Takeaways from the table.**
- Clique coordinates recover ω(G) exactly. Odd-cycle coordinates recover og(G) exactly.
- Bipartite tests are useless.
- Only "structured" non-bipartite tests carry finer information: Petersen, Kneser, Mycielski, circulants, and the n ≤ 9 cores themselves.
- This is the profile counterpart of D's observation that triangle violations are driven by edge mass.

---

## 3. Applications

1. **Coordinates for the homomorphism order.** Prop. O makes φ an order-embedding of the hom-lattice of 𝔉-cores into a cube.
   - Agent R can test MDS or PCA on φ to see whether the first principal axes are ω, og and χ-like (cf. the closed forms).
   - Can a "density" result à la Welzl be read off as interpolation of profiles?
2. **CSP approximability, the FJT programme for free.** If Max-M-Col is α-approximable, then Max-N-Col is (1−d)·α-approximable, with d the Hilbert/FJT distance (FJT Lemma 5).
   - Using finite 𝔉 gives *upper* bounds s_𝔉 ≥ s. These are certificates of non-approximability transfer, and computable bounds on FJT distances for the repo's 1276 cores.
   - Concretely, one could tabulate s_𝔉(K2,H) ≈ bipartite-density-type numbers, and so the Goemans–Williamson-transferred ratio 0.878·s(K2,H)... for all cores n ≤ 9.
3. **Graph features / kernels.** The (max,+) DP (Prop. T) gives φ on treewidth-bounded test families in polynomial time.
   - **Caveat:** for large real-world target graphs with ω ≥ 4, every test T with χ(T) ≤ ω maps in, so the profile is near zero. The informative ML object is then the *source* profile ψ(G) = (α(G,H)/e(G))_{H small}: Max-Cut ratio, Max-3-Cut ratio, |G,C5|/e, |G,Petersen|/e, …
   - ψ is Lipschitz under edge edits (1 edit changes α by ≤ 1). It could be compared against hom-count features (NT–Maehara) on TU benchmarks.
   - **Recommend that P/Q also define ψ**, the dual (source-side) profile.
4. **Conjecture testing.**
   - (a) "Profile Hedetniemi" (Prop. P).
   - (b) Odd-girth or circular-chromatic bounds as linear inequalities among coordinates, e.g. φ(G)_{C5} = 0 ⇒ φ(G)_{Petersen} ≤ 2/15? Pentagon/Jaeger-type statements from open_problems/ ask whether specific coordinates vanish (e.g. "P → G for all cubic G of large girth" in the pentagon problem is a statement about a φ(G)_P coordinate).
   - (c) Linear relations: is the convex hull of {φ(G)} over cores polyhedral? This is the analogue of the Razborov / graph-profile region for hom densities.
5. **Graph limits.** By BCLSV cut-continuity [V, abstract], φ(G)_W := 1 − Ê(W; A_G)/t(K2,W) extends φ to graphon tests W (Prop. G). The table rows for dense random graphs are instances of this.

---

## 4. How to present it in the paper

The place is a new section after `sec:metric` (the m(G,H) section), titled **"The α-profile and metrics on homomorphism classes"**. It also replaces `q:metric`. D_round2 shows q:metric(a) equals |G,H|, and (b) fails under padding.

**Figure suggestion.**
- (i) A heatmap of φ for small cores, with columns = tests (K3, K4, K5, C5, C7, P, Grötzsch, …) and rows = targets.
- (ii) 2-D MDS of E on the 85 cores, coloured by χ, with arrows for the Hasse diagram of →. This shows monotonicity: arrows point "down" in φ.

Agent R/Q's C_mds.png and E_euclid_n8.png from round 1 are near this already.

**Draft LaTeX.**
```latex
\section{The $\alpha$-profile of a graph}\label{sec:profile}

\begin{definition}[$\alpha$-profile]
Let $\mathfrak F$ be a countable family of graphs with at least one edge
(\emph{test graphs}) and $w:\mathfrak F\to(0,\infty)$ with
$\sum_{T}w_T<\infty$. For a graph $G$ the \emph{$\alpha$-profile} is
\[
  \varphi(G)=\Bigl(\tfrac{|T,G|}{|E(T)|}\Bigr)_{T\in\mathfrak F}\in[0,1]^{\mathfrak F},
\]
and the \emph{profile distance} is
$E_w(G,H)=\bigl(\sum_{T}w_T(\varphi(G)_T-\varphi(H)_T)^2\bigr)^{1/2}$.
\end{definition}

\begin{proposition}[invariance and monotonicity]\label{prop:prof_mono}
If $G\to H$ then $\varphi(G)\ge\varphi(H)$ coordinatewise. In particular
$\varphi$ is constant on homomorphism classes.
\end{proposition}

\begin{proposition}[order embedding]\label{prop:prof_embed}
If $\mathfrak F$ contains the cores of $G$ and $H$, then
$G\to H \iff \varphi(H)\le\varphi(G)$. Consequently $E_w$ and
$\|\varphi(G)-\varphi(H)\|_\infty$ are metrics on the homomorphism classes
of $\mathfrak F$-cores.
\end{proposition}

\begin{proposition}[tropical homomorphism numbers]\label{prop:prof_trop}
Let $W_\beta(G)$ be the weighted looped complete graph on $V(G)$ with weight
$e^\beta$ on $E(G)$ and $1$ elsewhere. Then
\[
 |E(T)|-|T,G| \;=\; \lim_{\beta\to\infty}\tfrac1\beta\log\hom\bigl(T,W_\beta(G)\bigr).
\]
Hence $\varphi(G)_T$ is computable in time $O(|V(T)|\,|V(G)|^{\mathrm{tw}(T)+1})$.
\end{proposition}

\begin{proposition}[cliques and odd cycles]\label{prop:prof_closed}
For every graph $G$ with $\omega(G)=r\ge 2$ and odd girth $g$,
\[
\varphi(G)_{K_n}=1-\frac{t(n,r)}{\binom n2},\qquad
\varphi(G)_{C_{2k+1}}=\begin{cases}0,& 2k+1\ge g,\\ \frac1{2k+1},&\text{otherwise.}\end{cases}
\]
In particular $\varphi$ determines $\omega(G)$ and the odd girth of $G$.
\end{proposition}

\begin{proposition}[relation to the FJT metric]\label{prop:prof_fjt}
Let $p_G=1-\varphi(G)$ over all edge-weighted test graphs. Then the
separation of F\"arnqvist--Jonsson--Thapper is
$s(G,H)=\inf_T p_G(T)/p_H(T)$, and
$-\log s(G,H)-\log s(H,G)$ is Hilbert's projective metric between
$p_G$ and $p_H$. For edge-transitive $T$, $\varphi(G)_T=1-s(G,T)$.
\end{proposition}

\begin{proposition}[Lipschitz bound via concentration]\label{prop:prof_lip}
If $f:T-S\to G$ is optimal with load $\mu(f)$, then
$|T,H|\le|T,G|+\mu(f)\,|G,H|$.
\end{proposition}
```
Prop. `prof_closed` strengthens `thm:lower_bound`. Replace χ(H) with ω(H) there: |G,H| ≥ e(G) − t(v(G), ω(H)), which is tight for all G = K_n and **all** H. This is a free improvement to the existing paper.

**Open questions for the section.**
1. *(Dimension)* What is the smallest finite 𝔉 such that φ|_𝔉 is injective on cores with ≤ n vertices? Is it much smaller than the set of all such cores?
2. *(Profile Hedetniemi)* Is φ(G×H)_T = max(φ(G)_T, φ(H)_T) for every connected T?
3. *(Profile region)* Describe the closure of {φ(G)} ⊂ [0,1]^𝔉 for 𝔉 = {K3, K4, C5, P}. Which linear inequalities hold (analogue of Razborov's flag-algebra regions)?
4. *(Indistinguishability)* For which families 𝔉 does φ|_𝔉(G) = φ|_𝔉(H) have a logical or algorithmic characterisation, analogous to Dell–Grohe–Rattan for trees and k-WL? Note: for bipartite-free / treewidth-≤2 families this reduces to the odd girth of G.
5. *(Comparison)* Are E_w, δ_𝔉 and d_Hilbert bi-Lipschitz equivalent on cores of bounded size? (The data: corr(d_𝔉, δ_𝔉) = 0.97, D_round2.)
6. *(Limits)* Describe the completion of (hom-classes, E_w) with graphon tests: e.g. K_n → "1/ω profile" sequences.

---

## 5. Notes for P, Q, R
- **P:** Props O, T, H and L are short. Please check the Hilbert identification against FJT's weighted definition. The inf must range over weighted T, or over simple graphs by D's graphon argument.
- **Q:**
  - Compute the smallest injective test family (OQ1).
  - Search for a connected counterexample to OQ2 among cores n ≤ 7.
  - Compute s_𝔉(K2,H) for all cores to give Goemans–Williamson-transferred ratios.
- **R:**
  - Check that the leading PCA axes of φ correlate with ω and og (Prop. closed).
  - Compare the ℓ2 (E) vs ℓ∞ vs Hilbert distances.
