# Lean 4 formalization of the |G,H| / γ(G,H) results

Lean `v4.35.0` with Mathlib `v4.35.0`. Build with:

```bash
cd lean/NonHom
lake exe cache get   # first time only: prebuilt Mathlib
lake build           # checks every proof
```

All proofs are complete: no `sorry`, no `native_decide`, no extra axioms
(`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`).
Finite checks use `decide +kernel`, which is verified by the Lean kernel.

`nhf G H : ℕ∞` is `|G,H|`, `gamma G H : ℕ∞` is `γ(G,H)` (`⊤` when no homomorphism exists),
`mu f` is the max edge load of a homomorphism, `msym` is `m(G,H)`. `K_n` is `⊤ : SimpleGraph (Fin n)`.

## Paper/paper.tex

| Statement | Lean | File |
|---|---|---|
| Prop `prop:chi_mono` | `chromaticNumber_le_of_hom` | Intro |
| Thm `thm:hom_contracts` | `edist_map_le`, `dist_map_le` | Intro |
| Prop `prop:monotone` (1)(2)(3) | `nhf_le_of_hom_target`, `nhf_eq_of_hom_equiv`, `nhf_le_of_edge_injective` | NHF |
| Thm `thm:KnKm` | `nhf_top_top`, `nhf_top_top_formula`, `nhf_top_succ_top` | Turan |
| Table `tab:KnKm` | `table_KnKm` | Metric |
| Thm `thm:lower_bound` | `lower_bound` | Turan |
| `|C_n,K_3| = 0`, `|C_n,K_2|` | `nhf_cycle_K3`, `nhf_cycle_K2_even`, `nhf_cycle_K2_odd` | Cycles, OpenProblems |
| Obs `obs:PK2` | `nhf_petersen_K2` | Petersen |
| Prop `prop:pigeonhole` | `ceil_div_le_gamma` | Gamma |
| Lemmas `lem:gamma_identity`, `lem:gamma_pos` | `gamma_self`, `one_le_gamma` | Gamma |
| Lemma `lem:gamma_mult` | `gamma_comp_le` | Gamma |
| Lemma `lem:nhf_bound` | `nhf_le_gamma_mul` | Gamma |
| Lemma `lem:two_sided` | `two_sided` | Gamma |
| Lemma `lem:gamma_mono` | `gamma_le_of_injective_hom`, `gamma_anti_target` | Gamma |
| Prop `prop:gamma_Kn` | `gamma_top_top_eq_one`, `gamma_top_top_eq_top` | Gamma |
| Thm `thm:d_regular` | `two_mu_eq` (exact identity), `gamma_K3_lower`, `gamma_K3_upper` | Regular |
| Prop `prop:m_zero` (first ⇔) | `msym_eq_zero_iff` | Metric |
| Thm `thm:no_triangle` | `no_triangle`, `msym_not_triangle` | Metric |
| Thm `thm:cycle_gamma` | `gamma_cycle` | Cycles |
| Thm `thm:Knn`, Table `tab:KnnK3` | `gamma_knn`, `nhf_knn_K3`, `table_KnnK3` | Bipartite |
| `γ(P,K₃) = 6`, `γ(P,K₅) = 2`, `γ(P,K₄) ≤ 4`, `χ(P) = 3`, `|P,K_m| = 0` | `gamma_petersen_K3`, `gamma_petersen_K5`, `gamma_petersen_K4_le`, `petersen_chromaticNumber`, `nhf_petersen_Km` | Petersen |
| Obs `obs:book` | `gamma_book`, `nhf_book_K2` | Families |
| Obs `obs:friendship_exact` | `gamma_friendship`, `nhf_friendship_K2` | Families |
| Obs `obs:wheel_gamma` | `gamma_wheel` | Families |
| Obs `obs:multipartite_gamma`, Table `tab:multipartite` (K₃ column) | `gamma_tri`, `table_multipartite` | Families |
| Obs `obs:CnC5_pattern` (general ⇔) | `cycle_hom_iff` | OddCycles |
| Tables `tab:CnC5`, `tab:CnC7` (selected rows) | `gamma_C6_C5`, `gamma_C8_C7`, `gamma_C10_C7`, `gamma_C12_C7`, `gamma_C15_C7` | OddCycles |

## Generalizations (added later)

| Statement | Lean | File |
|---|---|---|
| `|K_n,H| = C(n,2) - t(n,ω(H))` | `nhf_top_clique` | Generalize |
| `|L(G),H| ≥ n(C(d,2) - t(d,r))` for `K_{r+1}`-free `H` | `line_lower_clique` | Generalize |
| Edge-transitive `G`, `F → G`, `F ↛ H`: `|E(G)| ≤ |E(F)|·|G,H|` | `nhf_edge_transitive` | Generalize |
| Averaging bound `|V(H)|²|G,H| ≤ |E(G)|(|V(H)|² - 2|E(H)|)` | `nhf_average` | Average |
| `γ(C_n,C_m)` for odd `m` = least `M ≡ n (mod 2)` with `mM ≥ n` | `gamma_cycle_cycle` | CycleCycle |
| `γ(G₁ + \bar K_k, K₃) = max(|E(G₁)|, k·β(G₁))` | `gamma_join` | Join |
| `|H(d,n),H| = d·n^{d-1}(C(n,2) - t(n,ω(H)))` (Hamming graphs) | `nhf_ham` | Hamming |
| `d`-regular with an equitable 3-colouring: `2γ(G,K₃) = d·M(n)` | `gamma_K3_equitable` | Equitable |
| Hypercubes `2γ(Q_d,K₃) = d·M(2^d)`, closed form | `gamma_cube`, `Mtri_two_pow` | Equitable |
| `|C_p×C_q,H| = 2p` for every `H` with an edge and `C_q ↛ H` (0 if `C_q → H`) | `nhf_tensor_cycles_target`, `nhf_tensor_cycles_zero`, `nhf_tensor_cycles_cycle` | TensorTarget |
| `d`-regular into odd `C_m`: `2L_c = d·s_c`, `2γ(G,C_m) ≥ d·M_m(n)`, equality criterion | `two_Lc`, `gamma_oddcycle_lower`, `gamma_oddcycle_upper` | OddTarget |
| Line graphs exact for every target given a proper `d`-edge-colouring | `nhf_line_class1` | LineExact |
| Folded cubes `|FQ_n,H| = 2^{n-2}` (odd `n`, `C_n ↛ H`) | `nhf_folded`, `nhf_folded_K2`, `nhf_folded_cycle` | FoldedCube |
| Triangular graphs into `K_r`: parity excess `r/2` (odd `n`, `n-1 = qr`, `q` odd); even `n` exact for every target | `tri_lower_parity`, `nhf_triangular_even` | TriangularR |
| Triangular graphs, odd `n`, `r ∣ n-1`: exact value with and without the `r/2` excess (explicit centre-class colouring, replaces Walecki) | `nhf_triangular_odd_div_even`, `nhf_triangular_odd_div_odd` | TriOddDiv |
| Triangular graphs, `r ∤ n-1`, any `n`: exact for every target of clique number `r` (explicit equitable colouring, replaces Hilton–de Werra) | `nhf_triangular_equitable` | TriEquitable |
| Triangular graphs, `r ≥ 3`: some target of clique number `r` reaches the Turán value for every `n` (parity excess is specific to `K_r`) | `nhf_triangular_general_target`, `nhf_triangular_general_target_edges` | TriGeneral |
| Spectral (Mohar–Poljak) bound in certificate form; `2n-2` and `dq` optimal; tight iff `n ≡ 1 mod 4` (J(n,2)), iff `k ∣ q` (Hamming) | `cutSize_le_of_lapForm_le`, `isLeast_triangular`, `exists_cutSize_triangular_eq_iff`, `isLeast_ham`, `exists_cutSize_ham_eq_iff` | Spectral |
| Triangular graphs `|L(K_n),K₂| = n⌊(n-2)²/4⌋ + [n ≡ 3 (mod 4)]` | `nhf_triangular` | Triangular |

## open_problems/

| Statement | Lean | File |
|---|---|---|
| Theorem 1 (Jaeger), disjoint-family form | `jaeger_lower` | Jaeger |
| Theorem 2 (quantitative Hedetniemi) | `hedetniemi_bound` | OpenProblems |
| Theorem 3, `|C_p×C_q,K₂| = 2p` | `nhf_tensor_cycles` | Theorem3 |
| Sage result 1 | `nhf_top_triangleFree` | OpenProblems |
| Sage result 2: lower bound / equality given a balanced 2-edge-colouring / cubic with a perfect matching | `line_lower'`, `line_eq`, `line_cubic_pm` | LineGraph |
| Sage section 3: proved lower bound `⌈n/2⌉` | `sq_lower` | SquaredCycle |

## Not formalized

* Thm `thm:vertex_trans` (cited from Hell–Nešetřil) and the "isomorphic cores" clause of
  `prop:m_zero`: Mathlib has no theory of cores.
* Exhaustive-search values: the lower bound γ(P,K₄) ≥ 4, the K₄ columns, the Kneser rows, `tab:CnP`,
  the 108 triples, and the data in `open_problems/data`.
* Jaeger Theorem 1 is proved for any family of disjoint vertex sets that are each left by one edge.
  The step "the leaf blocks of the bridge-block tree form such a family" is not formalized.
* Sage result 2, upper bound: existence of the balanced colouring (Petersen's 2-factor theorem,
  König's theorem, Petersen's perfect-matching theorem) is assumed as a hypothesis.
* All statements labelled Conjecture.
