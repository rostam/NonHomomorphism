import NonHom.Hamming
import NonHom.Triangular

/-!
# Spectral (Mohar–Poljak) bounds for max-cut, `J(n,2)` and `H(d,q)`

Paper, Corollary `cor:spectral`, made eigenvalue-free.

* `cutSize_le_of_lapForm_le`: if `xᵀ L_G x ≤ λ ‖x‖²` for all `x` (e.g. `λ I - L_G ⪰ 0`,
  `lapForm_le_of_posSemidef`), every `k`-colouring cuts `≤ (k-1)/(2k) · λ · |V|` edges;
  `le_nhf_of_lapForm_le` turns this into a lower bound on `|G, K_k|`.
* Clique covers (`lapForm_eq_of_cliqueCover`): `xᵀ L x = m r ‖x‖² - ∑_i (∑_{C_i} x)²`.
* `L(G)`, `G` `d`-regular: `λ_max ≤ 2d` (stars), with equality witnessed by a 4-cycle.
  For `J(n,2) = L(K_n)`: `cutSize_triangular_le` (`≤ n(n-1)²/4`), `isLeast_triangular`
  (`2n-2` is optimal), `exists_cutSize_triangular_eq_iff` (tight iff `n ≡ 1 mod 4`).
* `H(d,q)`: `λ_max = d q` (lines), `cutSize_ham_le`, `isLeast_ham`,
  `exists_cutSize_ham_eq_iff` (max-`k`-cut bound tight iff `k ∣ q`).
-/

open SimpleGraph Finset

namespace NonHom

section general

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The Laplacian quadratic form `xᵀ L_G x = ½ ∑_{u ~ v} (x u - x v)²` (ordered pairs). -/
noncomputable def lapForm (x : V → ℝ) : ℝ :=
  (∑ u, ∑ v, if G.Adj u v then (x u - x v) ^ 2 else 0) / 2

theorem lapForm_eq_toLinearMap₂' (x : V → ℝ) :
    lapForm G x = Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) x x :=
  (G.lapMatrix_toLinearMap₂' ℝ x).symm

/-- The matrix form of the certificate: `λ I - L_G ⪰ 0` gives `xᵀ L_G x ≤ λ ‖x‖²`. -/
theorem lapForm_le_of_posSemidef (lam : ℝ)
    (h : (lam • (1 : Matrix V V ℝ) - G.lapMatrix ℝ).PosSemidef) (x : V → ℝ) :
    lapForm G x ≤ lam * ∑ v, x v ^ 2 := by
  have h1 := h.dotProduct_mulVec_nonneg x
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, ← Matrix.toLinearMap₂'_apply', ← lapForm_eq_toLinearMap₂'] at h1
  simp only [dotProduct, smul_eq_mul, sq] at h1 ⊢
  linarith

/-- The edges of `G` cut by a colouring `c`. -/
def cutGraph {k : ℕ} (c : V → Fin k) : SimpleGraph V := G ⊓ (⊤ : SimpleGraph (Fin k)).comap c

instance {k : ℕ} (c : V → Fin k) : DecidableRel (cutGraph G c).Adj := fun u v =>
  inferInstanceAs (Decidable (G.Adj u v ∧ c u ≠ c v))

/-- The number of edges of `G` whose ends get different colours under `c`. -/
def cutSize {k : ℕ} (c : V → Fin k) : ℕ := (cutGraph G c).edgeFinset.card

omit [DecidableEq V] in
theorem sum_cut_pairs {k : ℕ} (c : V → Fin k) :
    (∑ u, ∑ v, if G.Adj u v ∧ c u ≠ c v then (1 : ℝ) else 0) = 2 * cutSize G c := by
  have h := (cutGraph G c).sum_degrees_eq_twice_card_edges
  unfold cutSize
  rw [← Nat.cast_ofNat, ← Nat.cast_mul, ← h, Nat.cast_sum]
  refine sum_congr rfl fun u _ => ?_
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, sum_boole]
  rfl

theorem sum_sq_indicator_diff {k : ℕ} (a b : Fin k) :
    (∑ j, ((if a = j then (1 : ℝ) else 0) - (if b = j then 1 else 0)) ^ 2) =
      if a = b then 0 else 2 := by
  by_cases h : a = b
  · subst h; simp
  · simp only [h, ↓reduceIte]
    have : ∀ j, ((if a = j then (1 : ℝ) else 0) - (if b = j then 1 else 0)) ^ 2 =
        (if a = j then 1 else 0) + (if b = j then 1 else 0) := by
      intro j; split_ifs <;> simp_all
    simp_rw [this, sum_add_distrib, sum_ite_eq, mem_univ, ite_true]
    norm_num

theorem sum_sq_indicator_sub {k : ℕ} (hk : 0 < k) (a : Fin k) :
    (∑ j : Fin k, ((if a = j then (1 : ℝ) else 0) - 1 / (k : ℝ)) ^ 2) = 1 - 1 / (k : ℝ) := by
  have : ∀ j : Fin k, ((if a = j then (1 : ℝ) else 0) - 1 / (k : ℝ)) ^ 2 =
      (if a = j then 1 - 2 / (k : ℝ) else 0) + 1 / (k : ℝ) ^ 2 := by
    intro j; split_ifs <;> ring
  simp_rw [this, sum_add_distrib, sum_ite_eq, mem_univ, ite_true, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have : (k : ℝ) ≠ 0 := by positivity
  field_simp
  ring

omit [DecidableEq V] in
/-- **Mohar–Poljak bound, certificate form, for max-`k`-cut.** If `xᵀ L_G x ≤ λ ‖x‖²` for every
real vector `x` (i.e. `λ I - L_G` is positive semidefinite), then every `k`-colouring of `V`
cuts at most `(k-1)/(2k) · λ · |V|` edges. -/
theorem cutSize_le_of_lapForm_le {k : ℕ} (hk : 0 < k) (lam : ℝ)
    (hQ : ∀ x : V → ℝ, lapForm G x ≤ lam * ∑ v, x v ^ 2) (c : V → Fin k) :
    (cutSize G c : ℝ) ≤ (k - 1) / (2 * k) * lam * Fintype.card V := by
  set x : Fin k → V → ℝ := fun j v => (if c v = j then 1 else 0) - 1 / k
  have hL : ∑ j, lapForm G (x j) = 2 * cutSize G c := by
    unfold lapForm
    rw [← sum_div, ← sum_cut_pairs]
    rw [sum_comm]
    simp_rw [sum_comm (s := (univ : Finset (Fin k)))]
    rw [div_eq_iff (by norm_num), sum_mul]
    refine sum_congr rfl fun u _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun v _ => ?_
    by_cases hadj : G.Adj u v
    · simp only [hadj, ite_true, true_and, x]
      have := sum_sq_indicator_diff (c u) (c v)
      simp only [sub_sub_sub_cancel_right] at *
      rw [this]; split_ifs <;> simp_all
    · simp [hadj]
  have hR : ∑ j, lam * ∑ v, x j v ^ 2 = lam * Fintype.card V * (1 - 1 / k) := by
    rw [← mul_sum, sum_comm]
    simp only [x, sum_sq_indicator_sub hk, sum_const, card_univ, nsmul_eq_mul]
    ring
  have h2 : 2 * (cutSize G c : ℝ) ≤ lam * Fintype.card V * (1 - 1 / k) := by
    rw [← hL, ← hR]; exact sum_le_sum fun j _ => hQ (x j)
  have : (k : ℝ) ≠ 0 := by positivity
  have hk' : (0 : ℝ) < k := by positivity
  rw [show (k - 1) / (2 * k) * lam * Fintype.card V = lam * Fintype.card V * (1 - 1 / k) / 2 by
    field_simp]
  linarith


/-- If `g` colours `G - S` properly, every edge outside `S` is cut by `g`. -/
theorem card_edgeFinset_le_cutSize_add {k : ℕ} (S : Finset (Sym2 V))
    (g : G.deleteEdges ↑S →g (⊤ : SimpleGraph (Fin k))) :
    G.edgeFinset.card ≤ cutSize G g + S.card := by
  have hsub : G.edgeFinset ⊆ (cutGraph G g).edgeFinset ∪ S := by
    intro e he
    rw [mem_union]
    by_cases hS : e ∈ S
    · exact Or.inr hS
    left
    rw [mem_edgeFinset] at he ⊢
    induction e using Sym2.ind with
    | _ u v =>
      have hadj : (G.deleteEdges ↑S).Adj u v := by
        rw [deleteEdges_adj]; exact ⟨he, hS⟩
      exact ⟨he, g.map_rel hadj⟩
  have h1 := (card_le_card hsub).trans (card_union_le _ _)
  exact (card_le_card hsub).trans (card_union_le _ _)

/-- Conversely, deleting the uncut edges makes `c` a proper colouring. -/
theorem nhf_le_card_sub_cutSize {k : ℕ} (c : V → Fin k) :
    nhf G (⊤ : SimpleGraph (Fin k)) ≤ ((G.edgeFinset.card - cutSize G c : ℕ) : ℕ∞) := by
  have hsub : (cutGraph G c).edgeFinset ⊆ G.edgeFinset := edgeFinset_mono inf_le_left
  have := nhf_le_card (G := G) (H := (⊤ : SimpleGraph (Fin k)))
    (G.edgeFinset \ (cutGraph G c).edgeFinset) ⟨⟨c, fun {u v} h => ?_⟩⟩
  · rwa [card_sdiff_of_subset hsub] at this
  rw [deleteEdges_adj] at h
  by_contra hc
  apply h.2
  rw [coe_sdiff, Set.mem_sdiff, mem_coe, mem_coe, mem_edgeFinset, mem_edgeFinset]
  exact ⟨h.1, fun h' => hc h'.2⟩

/-- The max-`k`-cut is attained: some colouring cuts `|E| - |G, K_k|` edges. -/
theorem exists_cutSize_add_nhf {k : ℕ} (hk : 0 < k) :
    ∃ c : V → Fin k, ((G.edgeFinset.card : ℕ) : ℕ∞) ≤ cutSize G c + nhf G (⊤ : SimpleGraph (Fin k)) := by
  have hfin : nhf G (⊤ : SimpleGraph (Fin k)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENat.natCast_ne_top G.edgeFinset.card) (nhf_le_card _ ⟨⟨fun _ => ⟨0, hk⟩, ?_⟩⟩)
    intro u v h
    rw [deleteEdges_adj] at h
    exact absurd (mem_coe.mpr (mem_edgeFinset.mpr h.1)) h.2
  obtain ⟨S, ⟨g⟩, hS⟩ := exists_nhf_eq hfin
  refine ⟨g, ?_⟩
  rw [← hS]
  exact_mod_cast card_edgeFinset_le_cutSize_add G S g

/-- Deleting `S` leaves a `k`-colourable graph only if `S` contains every edge not cut by the
colouring; hence `|E(G)| - |S| ≤ cut ≤ (k-1)/(2k)·λ·|V|`. -/
theorem card_sub_le_of_lapForm_le {k : ℕ} (hk : 0 < k) (lam : ℝ)
    (hQ : ∀ x : V → ℝ, lapForm G x ≤ lam * ∑ v, x v ^ 2) (S : Finset (Sym2 V))
    (g : G.deleteEdges ↑S →g (⊤ : SimpleGraph (Fin k))) :
    (G.edgeFinset.card : ℝ) - (k - 1) / (2 * k) * lam * Fintype.card V ≤ S.card := by
  have h1 := card_edgeFinset_le_cutSize_add G S g
  have h2 := cutSize_le_of_lapForm_le G hk lam hQ g
  have : (G.edgeFinset.card : ℝ) ≤ cutSize G g + S.card := by exact_mod_cast h1
  linarith

/-- The `ℕ∞` form: a spectral certificate gives a lower bound on `|G, K_k|`. -/
theorem le_nhf_of_lapForm_le {k : ℕ} (hk : 0 < k) (lam : ℝ)
    (hQ : ∀ x : V → ℝ, lapForm G x ≤ lam * ∑ v, x v ^ 2) (m : ℕ)
    (hm : (m : ℝ) ≤ G.edgeFinset.card - (k - 1) / (2 * k) * lam * Fintype.card V) :
    (m : ℕ∞) ≤ nhf G (⊤ : SimpleGraph (Fin k)) := by
  apply le_nhf
  rintro S ⟨g⟩
  have := card_sub_le_of_lapForm_le G hk lam hQ S g
  have : m ≤ S.card := by exact_mod_cast hm.trans this
  exact_mod_cast this

/-! ### Clique covers

If every edge of `G` lies in exactly one of the cliques `C i`, non-edges in none, every clique
has `m` vertices and every vertex lies in `r` cliques, then
`xᵀ L_G x = m r ‖x‖² - ∑_i (∑_{v ∈ C i} x v)²`, so `λ_max(L_G) ≤ m r`. -/

omit [Fintype V] [DecidableEq V] in
theorem sum_sum_sq_sub (s : Finset V) (x : V → ℝ) :
    ∑ u ∈ s, ∑ v ∈ s, (x u - x v) ^ 2 = 2 * s.card * ∑ u ∈ s, x u ^ 2 - 2 * (∑ u ∈ s, x u) ^ 2 := by
  simp_rw [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, sq (∑ u ∈ s, x u),
    sum_mul_sum, ← mul_sum, ← sum_mul]
  rw [← Finset.mul_sum]
  ring

variable {I : Type*} [Fintype I] (C : I → Finset V)

theorem sum_adj_eq_sum_cliques
    (hpair : ∀ u v, u ≠ v → (univ.filter fun i => u ∈ C i ∧ v ∈ C i).card = if G.Adj u v then 1 else 0)
    (f : V → V → ℝ) (hf : ∀ u, f u u = 0) :
    (∑ u, ∑ v, if G.Adj u v then f u v else 0) = ∑ i, ∑ u ∈ C i, ∑ v ∈ C i, f u v := by
  have e1 : ∀ i, ∑ u ∈ C i, ∑ v ∈ C i, f u v =
      ∑ u, ∑ v, if u ∈ C i ∧ v ∈ C i then f u v else 0 := by
    intro i
    rw [← sum_ite_mem_eq]
    refine sum_congr rfl fun u _ => ?_
    rw [← sum_ite_mem_eq]
    split_ifs <;> simp_all
  rw [sum_congr rfl fun i _ => e1 i]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  by_cases huv : u = v
  · subst huv; simp [hf]
  · rw [hpair u v huv]
    split_ifs <;> simp


/-- **Clique-cover identity.** `xᵀ L_G x = m r ‖x‖² - ∑_i (∑_{v ∈ C i} x v)²`. -/
theorem lapForm_eq_of_cliqueCover (m r : ℕ)
    (hpair : ∀ u v, u ≠ v → (univ.filter fun i => u ∈ C i ∧ v ∈ C i).card = if G.Adj u v then 1 else 0)
    (hsize : ∀ i, (C i).card = m) (hmult : ∀ v, (univ.filter fun i => v ∈ C i).card = r)
    (x : V → ℝ) :
    lapForm G x = m * r * ∑ v, x v ^ 2 - ∑ i, (∑ v ∈ C i, x v) ^ 2 := by
  unfold lapForm
  rw [sum_adj_eq_sum_cliques G C hpair (fun u v => (x u - x v) ^ 2) (fun u => by simp)]
  simp_rw [sum_sum_sq_sub, hsize]
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum]
  have key : ∑ i, ∑ v ∈ C i, x v ^ 2 = r * ∑ v, x v ^ 2 := by
    rw [sum_congr rfl fun i _ => (sum_ite_mem_eq (C i) fun v => x v ^ 2).symm, sum_comm, mul_sum]
    refine sum_congr rfl fun v _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul, hmult]
  rw [key]
  ring

/-- Edge count from a clique cover: `2 |E| = |I| m (m - 1)`. -/
theorem two_mul_card_edgeFinset_of_cliqueCover (m : ℕ)
    (hpair : ∀ u v, u ≠ v → (univ.filter fun i => u ∈ C i ∧ v ∈ C i).card = if G.Adj u v then 1 else 0)
    (hsize : ∀ i, (C i).card = m) :
    (2 * G.edgeFinset.card : ℝ) = Fintype.card I * (m * (m - 1)) := by
  have h := G.sum_degrees_eq_twice_card_edges
  have h2 : (∑ u, ∑ v, if G.Adj u v then (if u = v then 0 else 1 : ℝ) else 0) =
      2 * G.edgeFinset.card := by
    rw [← Nat.cast_ofNat, ← Nat.cast_mul, ← h, Nat.cast_sum]
    refine sum_congr rfl fun u _ => ?_
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, ← sum_boole]
    refine sum_congr rfl fun v _ => ?_
    by_cases huv : G.Adj u v
    · simp [huv, huv.ne]
    · simp [huv]
  rw [← h2, sum_adj_eq_sum_cliques G C hpair _ (fun u => by simp)]
  have : ∀ i, ∑ u ∈ C i, ∑ v ∈ C i, (if u = v then 0 else 1 : ℝ) = m * (m - 1) := by
    intro i
    have : ∀ u ∈ C i, ∑ v ∈ C i, (if u = v then 0 else 1 : ℝ) = m - 1 := by
      intro u hu
      have : ∀ v, (if u = v then 0 else 1 : ℝ) = 1 - if u = v then 1 else 0 := by
        intro v; split_ifs <;> simp
      simp_rw [this, sum_sub_distrib, sum_ite_eq, hu, ite_true, sum_const, hsize, nsmul_eq_mul,
        mul_one]
    rw [sum_congr rfl this, sum_const, hsize, nsmul_eq_mul]
  rw [sum_congr rfl fun i _ => this i, sum_const, card_univ, nsmul_eq_mul]

/-- **Clique-cover bound.** `xᵀ L_G x ≤ m r ‖x‖²`, i.e. `λ_max(L_G) ≤ m r`. -/
theorem lapForm_le_of_cliqueCover (m r : ℕ)
    (hpair : ∀ u v, u ≠ v → (univ.filter fun i => u ∈ C i ∧ v ∈ C i).card = if G.Adj u v then 1 else 0)
    (hsize : ∀ i, (C i).card = m) (hmult : ∀ v, (univ.filter fun i => v ∈ C i).card = r)
    (x : V → ℝ) :
    lapForm G x ≤ m * r * ∑ v, x v ^ 2 := by
  rw [lapForm_eq_of_cliqueCover G C m r hpair hsize hmult]
  have : 0 ≤ ∑ i, (∑ v ∈ C i, x v) ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  linarith

end general

/-! ### Line graphs of regular graphs: `λ_max(L_{L(G)}) ≤ 2d` -/

section lineGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

instance lineGraphDecRel : DecidableRel G.lineGraph.Adj := fun e f =>
  decidable_of_iff (e ≠ f ∧ ∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V))
    lineGraph_adj_iff_exists.symm

/-- The star of `v`: edges of `G` at `v`, a clique of `L(G)`. -/
def edgeStar (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset G.edgeSet :=
  univ.filter fun e => v ∈ (e : Sym2 V)

theorem card_edgeStar {d : ℕ} (hreg : G.IsRegularOfDegree d) (v : V) : (edgeStar G v).card = d := by
  rw [← card_At hreg v, Fintype.card_subtype]
  rfl

theorem card_filter_mem_edgeStar (e : G.edgeSet) : (univ.filter fun v => e ∈ edgeStar G v).card = 2 := by
  have : (univ.filter fun v => e ∈ edgeStar G v) = (e : Sym2 V).toFinset := by
    ext v; simp [edgeStar]
  rw [this, Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeSet e.2)]

theorem card_filter_mem_edgeStar_pair (e f : G.edgeSet) (hef : e ≠ f) :
    (univ.filter fun v => e ∈ edgeStar G v ∧ f ∈ edgeStar G v).card =
      if G.lineGraph.Adj e f then 1 else 0 := by
  simp only [edgeStar, mem_filter, mem_univ, true_and]
  split_ifs with h
  · rw [lineGraph_adj_iff_exists] at h
    obtain ⟨-, v, hve, hvf⟩ := h
    rw [card_eq_one]
    refine ⟨v, ?_⟩
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    refine ⟨fun ⟨hwe, hwf⟩ => ?_, fun h => h ▸ ⟨hve, hvf⟩⟩
    by_contra hwv
    have h1 := (Sym2.mem_and_mem_iff hwv).mp ⟨hwe, hve⟩
    have h2 := (Sym2.mem_and_mem_iff hwv).mp ⟨hwf, hvf⟩
    exact hef (Subtype.ext (h1.trans h2.symm))
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro v - ⟨hve, hvf⟩
    exact h (lineGraph_adj_iff_exists.mpr ⟨hef, v, hve, hvf⟩)

/-- For `d`-regular `G`: `xᵀ L_{L(G)} x = 2d ‖x‖² - ∑_v (∑_{e ∋ v} x e)²` (this is
`A_{L(G)} = BᵀB - 2I` with `B` the vertex-edge incidence matrix). -/
theorem lapForm_lineGraph_eq {d : ℕ} (hreg : G.IsRegularOfDegree d) (x : G.edgeSet → ℝ) :
    lapForm G.lineGraph x = 2 * d * ∑ e, x e ^ 2 - ∑ v, (∑ e ∈ edgeStar G v, x e) ^ 2 := by
  rw [lapForm_eq_of_cliqueCover G.lineGraph (edgeStar G) d 2 card_filter_mem_edgeStar_pair
    (card_edgeStar hreg) card_filter_mem_edgeStar]
  push_cast; ring

/-- For `d`-regular `G`: `λ_max(L_{L(G)}) ≤ 2d`. -/
theorem lapForm_lineGraph_le {d : ℕ} (hreg : G.IsRegularOfDegree d) (x : G.edgeSet → ℝ) :
    lapForm G.lineGraph x ≤ 2 * d * ∑ e, x e ^ 2 := by
  rw [lapForm_lineGraph_eq hreg]
  have : 0 ≤ ∑ v, (∑ e ∈ edgeStar G v, x e) ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  linarith

/-- A 4-cycle `a b c d` of `G` gives a vector (`+1` on `ab, cd`, `-1` on `bc, da`) with zero
sum at every vertex, so `xᵀ L_{L(G)} x = 2d ‖x‖²`: the bound `2d` is the top eigenvalue. -/
theorem exists_lapForm_lineGraph_eq {d : ℕ} (hreg : G.IsRegularOfDegree d) {a b c e : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hce : G.Adj c e) (hea : G.Adj e a)
    (hac : a ≠ c) (hbe : b ≠ e) :
    ∃ x : G.edgeSet → ℝ, x ≠ 0 ∧ lapForm G.lineGraph x = 2 * d * ∑ f, x f ^ 2 := by
  let E1 : G.edgeSet := ⟨s(a, b), hab⟩
  let E2 : G.edgeSet := ⟨s(c, e), hce⟩
  let E3 : G.edgeSet := ⟨s(b, c), hbc⟩
  let E4 : G.edgeSet := ⟨s(e, a), hea⟩
  let x : G.edgeSet → ℝ := fun f => (if f = E1 then 1 else 0) + (if f = E2 then 1 else 0) -
    (if f = E3 then 1 else 0) - (if f = E4 then 1 else 0)
  have hne := hab.ne
  have hne2 := hbc.ne
  have hne3 := hce.ne
  have hne4 := hea.ne
  refine ⟨x, fun h => ?_, ?_⟩
  · have h1 := congrFun h E1
    have h12 : E1 ≠ E2 := by
      intro h; have := congrArg Subtype.val h
      simp only [E1, E2, Sym2.eq_iff] at this; tauto
    have h13 : E1 ≠ E3 := by
      intro h; have := congrArg Subtype.val h
      simp only [E1, E3, Sym2.eq_iff] at this; tauto
    have h14 : E1 ≠ E4 := by
      intro h; have := congrArg Subtype.val h
      simp only [E1, E4, Sym2.eq_iff] at this; tauto
    simp [x, h12, h13, h14] at h1
  · rw [lapForm_lineGraph_eq hreg]
    have : ∀ v, ∑ f ∈ edgeStar G v, x f = 0 := by
      intro v
      simp only [x, sum_add_distrib, sum_sub_distrib, sum_ite_eq', edgeStar, mem_filter, mem_univ,
        true_and, E1, E2, E3, E4, Sym2.mem_iff]
      by_cases h1 : v = a <;> by_cases h2 : v = b <;> by_cases h3 : v = c <;>
        by_cases h4 : v = e <;> simp_all
    simp [this]

end lineGraph

/-! ### Triangular graphs `J(n,2) = L(K_n)` -/

section triangular

local notation "Kn" n => (⊤ : SimpleGraph (Fin n))

/-- `λ_max(L_{J(n,2)}) ≤ 2n - 2`. -/
theorem lapForm_triangular_le (n : ℕ) (x : (Kn n).edgeSet → ℝ) :
    lapForm (Kn n).lineGraph x ≤ 2 * ((n - 1 : ℕ) : ℝ) * ∑ e, x e ^ 2 :=
  lapForm_lineGraph_le (top_regular n) x

theorem card_edgeSet_top (n : ℕ) : Fintype.card (Kn n).edgeSet = n.choose 2 := by
  rw [← edgeFinset_card, card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]

/-- **Lean-verified Mohar–Poljak bound for `J(n,2)`**: every cut of `L(K_n)` has at most
`n (n-1)² / 4` edges. -/
theorem cutSize_triangular_le (n : ℕ) (hn : 1 ≤ n) (c : (Kn n).edgeSet → Fin 2) :
    (cutSize (Kn n).lineGraph c : ℝ) ≤ n * (n - 1) ^ 2 / 4 := by
  have h := cutSize_le_of_lapForm_le (Kn n).lineGraph (k := 2) (by norm_num) _
    (lapForm_triangular_le n) c
  rw [card_edgeSet_top, Nat.cast_choose_two, Nat.cast_sub hn] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

/-- `2n - 2` is the least valid certificate (the top Laplacian eigenvalue) for `n ≥ 4`. -/
theorem isLeast_triangular (n : ℕ) (hn : 4 ≤ n) :
    IsLeast {lam : ℝ | ∀ x : (Kn n).edgeSet → ℝ, lapForm (Kn n).lineGraph x ≤ lam * ∑ e, x e ^ 2}
      (2 * ((n - 1 : ℕ) : ℝ)) := by
  refine ⟨lapForm_triangular_le n, fun lam hlam => ?_⟩
  obtain ⟨x, hx, heq⟩ := exists_lapForm_lineGraph_eq (top_regular n)
    (a := ⟨0, by omega⟩) (b := ⟨1, by omega⟩) (c := ⟨2, by omega⟩) (e := ⟨3, by omega⟩)
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
  have hpos : 0 < ∑ e, x e ^ 2 := by
    obtain ⟨f, hf⟩ := Function.ne_iff.mp hx
    exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hf))) (single_le_sum (fun i _ => sq_nonneg (x i)) (mem_univ f))
  have := hlam x
  rw [heq] at this
  exact le_of_mul_le_mul_right this hpos

theorem two_mul_card_edgeFinset_triangular (n : ℕ) (hn : 1 ≤ n) :
    (2 * (Kn n).lineGraph.edgeFinset.card : ℝ) = n * (n - 1) * (n - 2) := by
  rw [two_mul_card_edgeFinset_of_cliqueCover (Kn n).lineGraph (edgeStar (Kn n)) (n - 1)
    card_filter_mem_edgeStar_pair (card_edgeStar (top_regular n)), Fintype.card_fin, Nat.cast_sub hn]
  push_cast; ring

/-- Arithmetic: `4 (n ⌊(n-2)²/4⌋ + [n ≡ 3 (mod 4)]) = n(n-1)(n-3)` iff `n ≡ 1 (mod 4)`. -/
theorem four_mul_tri_eq_iff (n : ℕ) (hn : 2 ≤ n) :
    (4 * ((n * ((n - 2) ^ 2 / 4) + (if n % 4 = 3 then 1 else 0) : ℕ) : ℝ) =
      n * (n - 1) * (n - 3)) ↔ n % 4 = 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  obtain ⟨t, s, hs, rfl⟩ : ∃ t s, s < 4 ∧ j = 4 * t + s := ⟨j / 4, j % 4, Nat.mod_lt _ (by norm_num),
    (Nat.div_add_mod j 4).symm⟩
  have hdiv : (4 * t + s + 2 - 2) ^ 2 / 4 = 4 * t ^ 2 + 2 * t * s + s ^ 2 / 4 := by
    rw [show (4 * t + s + 2 - 2) ^ 2 = s ^ 2 + 4 * (4 * t ^ 2 + 2 * t * s) by
      rw [Nat.add_sub_cancel]; ring, Nat.add_mul_div_left _ _ (by norm_num)]
    ring
  rw [hdiv]
  interval_cases s
  · simp only [show ¬ (4 * t + 0 + 2) % 4 = 3 by omega, show ¬ (4 * t + 0 + 2) % 4 = 1 by omega,
      ↓reduceIte, iff_false]
    push_cast; norm_num; nlinarith
  · simp only [show (4 * t + 1 + 2) % 4 = 3 by omega, ↓reduceIte]
    push_cast; norm_num; nlinarith
  · simp only [show ¬ (4 * t + 2 + 2) % 4 = 3 by omega, show ¬ (4 * t + 2 + 2) % 4 = 1 by omega,
      ↓reduceIte, iff_false]
    push_cast; norm_num; nlinarith
  · simp only [show (4 * t + 3 + 2) % 4 = 1 by omega, iff_true]
    push_cast; norm_num; ring

/-- **When is the Mohar–Poljak bound tight for `J(n,2)`?** Some cut of `L(K_n)` has exactly
`n (n-1)² / 4` edges iff `n ≡ 1 (mod 4)` (combining the spectral bound with `nhf_triangular`). -/
theorem exists_cutSize_triangular_eq_iff (n : ℕ) (hn : 2 ≤ n) :
    (∃ c : (Kn n).edgeSet → Fin 2, (cutSize (Kn n).lineGraph c : ℝ) = n * (n - 1) ^ 2 / 4) ↔
      n % 4 = 1 := by
  set N := n * ((n - 2) ^ 2 / 4) + (if n % 4 = 3 then 1 else 0)
  set E := (Kn n).lineGraph.edgeFinset.card
  have hE := two_mul_card_edgeFinset_triangular n (by omega)
  have hupper : ∀ c : (Kn n).edgeSet → Fin 2, cutSize (Kn n).lineGraph c + N ≤ E := by
    intro c
    have h1 := nhf_le_card_sub_cutSize (Kn n).lineGraph c
    rw [nhf_triangular n hn] at h1
    have h2 : cutSize (Kn n).lineGraph c ≤ E := card_le_card (edgeFinset_mono inf_le_left)
    have : N ≤ E - cutSize (Kn n).lineGraph c := by exact_mod_cast h1
    omega
  obtain ⟨c₀, hc₀⟩ := exists_cutSize_add_nhf (Kn n).lineGraph (k := 2) (by norm_num)
  rw [nhf_triangular n hn] at hc₀
  have hc₀' : E ≤ cutSize (Kn n).lineGraph c₀ + N := by exact_mod_cast hc₀
  have hmax : cutSize (Kn n).lineGraph c₀ + N = E := le_antisymm (hupper c₀) hc₀'
  rw [← four_mul_tri_eq_iff n hn]
  have hcast : (cutSize (Kn n).lineGraph c₀ : ℝ) + N = E := by exact_mod_cast hmax
  constructor
  · rintro ⟨c, hc⟩
    have h1 : (cutSize (Kn n).lineGraph c : ℝ) + N ≤ E := by exact_mod_cast hupper c
    have h2 := cutSize_triangular_le n (by omega) c₀
    apply le_antisymm
    · nlinarith
    · nlinarith
  · intro h
    refine ⟨c₀, ?_⟩
    nlinarith

end triangular


/-! ### Hamming graphs `H(d,q) = K_q^{□d}`: `λ_max = d q` -/

section hamming

variable {d q : ℕ}

/-- The vertex set of a line. -/
def lineSet [NeZero q] (p : Lines d q) : Finset (Fin d → Fin q) :=
  univ.image (lineMap p.1.1 p.1.2)

theorem mem_lineSet [NeZero q] (p : Lines d q) (w : Fin d → Fin q) :
    w ∈ lineSet p ↔ ∀ j, j ≠ p.1.1 → w j = p.1.2 j := by
  simp only [lineSet, mem_image, mem_univ, true_and, lineMap]
  constructor
  · rintro ⟨a, rfl⟩ j hj
    exact Function.update_of_ne hj _ _
  · intro h
    refine ⟨w p.1.1, funext fun j => ?_⟩
    by_cases hj : j = p.1.1
    · subst hj; simp
    · rw [Function.update_of_ne hj, h j hj]

theorem ham_adj_of_agree {u v : Fin d → Fin q} (j : Fin d) (h : ∀ k, k ≠ j → u k = v k)
    (hne : u ≠ v) : (ham d q).Adj u v := by
  show (univ.filter fun i => u i ≠ v i).card = 1
  rw [card_eq_one]
  refine ⟨j, ?_⟩
  ext k
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro hk; by_contra hkj; exact hk (h k hkj)
  · intro hkj hj
    rw [hkj] at hj
    apply hne
    funext m
    by_cases hm : m = j
    · rw [hm]; exact hj
    · exact h m hm

theorem card_lineSet [NeZero q] (p : Lines d q) : (lineSet p).card = q := by
  rw [lineSet, card_image_of_injective _ (lineMap_injective _ _), card_univ, Fintype.card_fin]

theorem card_filter_mem_lineSet [NeZero q] (w : Fin d → Fin q) :
    (univ.filter fun p : Lines d q => w ∈ lineSet p).card = d := by
  refine Eq.trans (b := (univ : Finset (Fin d)).card) ?_ (by simp)
  refine card_nbij' (fun p => p.1.1) (fun i => ⟨(i, Function.update w i 0), by simp⟩)
    (fun _ _ => mem_univ _) (fun i _ => ?_) (fun p hp => ?_) (fun i _ => rfl)
  · rw [mem_coe, mem_filter, mem_lineSet]
    exact ⟨mem_univ _, fun j hj => (Function.update_of_ne hj _ _).symm⟩
  · rw [mem_coe, mem_filter, mem_lineSet] at hp
    obtain ⟨⟨i, z⟩, hz⟩ := p
    simp only at hp ⊢
    congr
    funext j
    have hz' : z i = 0 := hz
    by_cases hj : j = i
    · subst hj; simp [hz']
    · rw [Function.update_of_ne hj, hp.2 j hj]

theorem card_filter_mem_lineSet_pair [NeZero q] (u v : Fin d → Fin q) (huv : u ≠ v) :
    (univ.filter fun p : Lines d q => u ∈ lineSet p ∧ v ∈ lineSet p).card =
      if (ham d q).Adj u v then 1 else 0 := by
  simp only [mem_lineSet]
  split_ifs with h
  · obtain ⟨i, hi, hv⟩ := ham_adj_line h
    rw [card_eq_one]
    refine ⟨⟨(i, Function.update u i 0), by simp⟩, ?_⟩
    ext ⟨⟨j, z⟩, hz⟩
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨hu, hv'⟩
      have hji : j = i := by
        by_contra hji
        exact hi ((hu i (Ne.symm hji)).trans (hv' i (Ne.symm hji)).symm)
      subst hji
      congr
      funext k
      have hz' : z j = 0 := hz
      by_cases hk : k = j
      · subst hk; simp [hz']
      · rw [Function.update_of_ne hk, hu k hk]
    · intro heq
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      refine ⟨fun k hk => (Function.update_of_ne hk _ _).symm, fun k hk => ?_⟩
      rw [Function.update_of_ne hk, hv, Function.update_of_ne hk]
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro ⟨⟨j, z⟩, hz⟩ - ⟨hu, hv⟩
    exact h (ham_adj_of_agree j (fun k hk => (hu k hk).trans (hv k hk).symm) huv)

/-- `xᵀ L_{H(d,q)} x = d q ‖x‖² - ∑_{lines ℓ} (∑_{w ∈ ℓ} x w)²`. -/
theorem lapForm_ham_eq [NeZero q] (x : (Fin d → Fin q) → ℝ) :
    lapForm (ham d q) x = d * q * ∑ w, x w ^ 2 - ∑ p : Lines d q, (∑ w ∈ lineSet p, x w) ^ 2 := by
  rw [lapForm_eq_of_cliqueCover (ham d q) lineSet q d card_filter_mem_lineSet_pair card_lineSet
    card_filter_mem_lineSet]
  ring

/-- `λ_max(L_{H(d,q)}) ≤ d q`. -/
theorem lapForm_ham_le [NeZero q] (x : (Fin d → Fin q) → ℝ) :
    lapForm (ham d q) x ≤ d * q * ∑ w, x w ^ 2 := by
  rw [lapForm_ham_eq]
  have : 0 ≤ ∑ p : Lines d q, (∑ w ∈ lineSet p, x w) ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  linarith

/-- **Lean-verified eigenvalue bound for max-`k`-cut of `H(d,q)`**: every `k`-colouring cuts at
most `(k-1)/(2k) · q^d · d q` edges. -/
theorem cutSize_ham_le [NeZero q] {k : ℕ} (hk : 0 < k) (c : (Fin d → Fin q) → Fin k) :
    (cutSize (ham d q) c : ℝ) ≤ (k - 1) / (2 * k) * q ^ d * (d * q) := by
  have h := cutSize_le_of_lapForm_le (ham d q) hk _ lapForm_ham_le c
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at h
  linarith

/-- The product vector `x(w) = ∏_i y(w_i)` with `y = e₀ - e₁` sums to zero on every line, so
`d q` is the least valid certificate (the top Laplacian eigenvalue) when `q ≥ 2`. -/
theorem isLeast_ham (hq : 2 ≤ q) :
    IsLeast {lam : ℝ | ∀ x : (Fin d → Fin q) → ℝ, lapForm (ham d q) x ≤ lam * ∑ w, x w ^ 2}
      (d * q) := by
  have : NeZero q := ⟨by omega⟩
  refine ⟨lapForm_ham_le, fun lam hlam => ?_⟩
  let o : Fin q := ⟨1, by omega⟩
  have ho : (0 : Fin q) ≠ o := by simp [o, Fin.ext_iff]
  let y : Fin q → ℝ := fun a => (if a = 0 then 1 else 0) - (if a = o then 1 else 0)
  let x : (Fin d → Fin q) → ℝ := fun w => ∏ i, y (w i)
  have hsum : ∀ p : Lines d q, ∑ w ∈ lineSet p, x w = 0 := by
    rintro ⟨⟨i, z⟩, hz⟩
    rw [lineSet, sum_image (fun a _ b _ h => lineMap_injective _ _ h)]
    have : ∀ a, x (lineMap i z a) = y a * ∏ j ∈ univ \ {i}, y (z j) := by
      intro a
      simp only [x, lineMap]
      change ∏ j, (y ∘ Function.update z i a) j = _
      rw [Function.comp_update, prod_update_of_mem (mem_univ i)]
      rfl
    simp only [this, ← sum_mul]
    simp [y, sum_sub_distrib]
  have heq : lapForm (ham d q) x = d * q * ∑ w, x w ^ 2 := by
    rw [lapForm_ham_eq]; simp [hsum]
  have hpos : 0 < ∑ w, x w ^ 2 := by
    have h0 : x 0 = 1 := by simp [x, y, ho]
    refine lt_of_lt_of_le ?_ (single_le_sum (fun i _ => sq_nonneg (x i)) (mem_univ 0))
    rw [h0]; norm_num
  have := hlam x
  rw [heq] at this
  exact le_of_mul_le_mul_right this hpos

theorem two_mul_card_edgeFinset_ham [NeZero q] (hd : 1 ≤ d) :
    (2 * (ham d q).edgeFinset.card : ℝ) = d * q ^ d * (q - 1) := by
  rw [two_mul_card_edgeFinset_of_cliqueCover (ham d q) lineSet q card_filter_mem_lineSet_pair
    card_lineSet, card_Lines]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  push_cast
  rw [pow_succ]
  ring

/-- `2 r · t(n, r) = (r - 1) n² - b (r - b)` where `b = n mod r` (Turán numbers). -/
theorem two_mul_turanNumber (n r : ℕ) (hr : 0 < r) :
    (2 * r * turanNumber n r : ℝ) = (r - 1) * n ^ 2 - (n % r : ℕ) * (r - (n % r : ℕ)) := by
  have key : ∀ a b, b < r →
      (2 * r * turanNumber (b + r * a) r : ℝ) = (r - 1) * ((b + r * a : ℕ) : ℝ) ^ 2 - b * (r - b) := by
    intro a b hb
    induction a with
    | zero =>
      have : turanNumber b r = b.choose 2 := by
        rw [turanNumber_eq, Nat.mod_eq_of_lt hb, Nat.sub_self, zero_mul, Nat.zero_div, zero_add]
      simp only [mul_zero, add_zero, this, Nat.cast_choose_two]
      ring
    | succ a ih =>
      rw [show b + r * (a + 1) = (b + r * a) + r by ring, turanNumber_add]
      push_cast [Nat.cast_choose_two]
      rw [Nat.cast_sub (by omega : 1 ≤ r)]
      push_cast at ih ⊢
      rw [mul_add, mul_add, ih]
      ring
  have := key (n / r) (n % r) (Nat.mod_lt _ hr)
  rwa [Nat.mod_add_div] at this

/-- **When is the eigenvalue max-`k`-cut bound tight for `H(d,q)`?** For `d ≥ 1`, some
`k`-colouring of `H(d,q)` cuts exactly `(k-1)/(2k) · q^d · d q` edges iff `k ∣ q`
(combining the spectral bound with `nhf_ham` and the Turán-number formula). -/
theorem exists_cutSize_ham_eq_iff [NeZero q] {k : ℕ} (hd : 1 ≤ d) (hk : 0 < k) :
    (∃ c : (Fin d → Fin q) → Fin k,
      (cutSize (ham d q) c : ℝ) = (k - 1) / (2 * k) * q ^ d * (d * q)) ↔ k ∣ q := by
  set N := d * q ^ (d - 1) * (q.choose 2 - turanNumber q k)
  set E := (ham d q).edgeFinset.card
  have hnhf : nhf (ham d q) (⊤ : SimpleGraph (Fin k)) = (N : ℕ∞) :=
    nhf_ham hk (cliqueFree_of_card_lt (by simp)) (SimpleGraph.Hom.id)
  have hupper : ∀ c : (Fin d → Fin q) → Fin k, cutSize (ham d q) c + N ≤ E := by
    intro c
    have h1 := nhf_le_card_sub_cutSize (ham d q) c
    rw [hnhf] at h1
    have h2 : cutSize (ham d q) c ≤ E := card_le_card (edgeFinset_mono inf_le_left)
    have : N ≤ E - cutSize (ham d q) c := by exact_mod_cast h1
    omega
  obtain ⟨c₀, hc₀⟩ := exists_cutSize_add_nhf (ham d q) hk
  rw [hnhf] at hc₀
  have hc₀' : E ≤ cutSize (ham d q) c₀ + N := by exact_mod_cast hc₀
  have hmax : (cutSize (ham d q) c₀ : ℝ) + N = E := by exact_mod_cast le_antisymm (hupper c₀) hc₀'
  -- the maximum cut is `d q^{d-1} t(q,k)`
  have hE := two_mul_card_edgeFinset_ham (q := q) hd
  have ht : turanNumber q k ≤ q.choose 2 := by
    have := card_edgeFinset_le_card_choose_two (G := turanGraph q k)
    simpa using this
  have hT := two_mul_turanNumber q k hk
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hN : (N : ℝ) = (e + 1) * q ^ e * (q * (q - 1) / 2 - turanNumber q k) := by
    simp only [N, Nat.add_sub_cancel]
    push_cast [Nat.cast_sub ht, Nat.cast_choose_two]
    ring
  have hM : (cutSize (ham (e + 1) q) c₀ : ℝ) = (e + 1) * q ^ e * turanNumber q k := by
    rw [pow_succ] at hE; push_cast at hE; nlinarith
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : (0 : ℝ) < (e + 1) * q ^ e := by positivity
  have hb : (q % k : ℕ) < k := Nat.mod_lt _ hk
  have hiff : ((e + 1) * q ^ e * turanNumber q k : ℝ) = (k - 1) / (2 * k) * q ^ (e + 1) * ((e + 1 : ℕ) * q)
      ↔ k ∣ q := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have hb' : ((q % k : ℕ) : ℝ) < k := by exact_mod_cast hb
    constructor
    · intro h
      have h2 : (2 * k * turanNumber q k : ℝ) = (k - 1) * q ^ 2 := by
        field_simp at h
        push_cast at h
        have : (e + 1) * q ^ e * (2 * k * turanNumber q k : ℝ) = (e + 1) * q ^ e * ((k - 1) * q ^ 2) := by
          rw [pow_succ] at h; nlinarith
        exact mul_left_cancel₀ hpos.ne' this
      rw [hT] at h2
      have h3 : ((q % k : ℕ) : ℝ) * (k - (q % k : ℕ)) = 0 := by linarith
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact_mod_cast h4
      · linarith
    · intro h
      rw [h] at hT
      push_cast at hT
      field_simp
      rw [pow_succ]
      push_cast
      have : (2 * k * turanNumber q k : ℝ) = (k - 1) * q ^ 2 := by linarith
      nlinarith
  rw [← hiff, ← hM]
  constructor
  · rintro ⟨c, hc⟩
    have h1 : (cutSize (ham (e + 1) q) c : ℝ) + N ≤ E := by exact_mod_cast hupper c
    have h2 := cutSize_ham_le (d := e + 1) hk c₀
    apply le_antisymm
    · push_cast at h2 ⊢; linarith
    · push_cast at hc ⊢; linarith
  · intro h
    exact ⟨c₀, by rw [h]⟩

end hamming

end NonHom
