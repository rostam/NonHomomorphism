import NonHom.Gamma

/-!
# The d-regularity formula (Theorem `thm:d_regular`)

For a `d`-regular `G` and a homomorphism `f : G → K₃` with colour classes of sizes
`a, b, c`, we prove the exact identity
`2·μ(f) = d · max(a+b-c, a+c-b, b+c-a)`,
from which the lower bound `γ(G,K₃) ≥ (d/2)·M` and the equality criterion follow.
-/

open SimpleGraph Finset

namespace NonHom

variable {V W : Type*} [Fintype V] [DecidableEq W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W}

/-- The load of `s(x,y)` equals the number of darts going from colour `x` to colour `y`. -/
theorem load_eq_card_darts (f : G →g H) {x y : W} (hxy : x ≠ y) :
    load f s(x, y) = (univ.filter fun d : G.Dart => f d.fst = x ∧ f d.snd = y).card := by
  classical
  unfold load
  symm
  apply Finset.card_bij (fun d _ => d.edge)
  · intro d hd
    simp only [mem_filter, mem_univ, true_and] at hd
    simp only [mem_filter, mem_edgeFinset]
    refine ⟨d.edge_mem, ?_⟩
    simp [Dart.edge, Sym2.map_mk, hd.1, hd.2]
  · intro d₁ h₁ d₂ h₂ h
    simp only [mem_filter, mem_univ, true_and] at h₁ h₂
    rcases (dart_edge_eq_iff d₁ d₂).mp h with h | h
    · exact h
    · exfalso; apply hxy
      have : d₁.fst = d₂.snd := by rw [h]; rfl
      rw [← h₁.1, this, h₂.2]
  · intro e he
    simp only [mem_filter, mem_edgeFinset] at he
    obtain ⟨he, hmap⟩ := he
    induction e using Sym2.ind with
    | _ u v =>
      rw [Sym2.map_mk, Sym2.eq_iff] at hmap
      rcases hmap with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨⟨(u, v), he⟩, by simp [h1, h2], rfl⟩
      · exact ⟨⟨(v, u), he.symm⟩, by simp [h1, h2], Sym2.eq_swap⟩

theorem card_darts_fst_color (f : G →g H) (x : W) :
    (univ.filter fun d : G.Dart => f d.fst = x).card =
      ∑ v ∈ univ.filter (fun v => f v = x), G.degree v := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun d : G.Dart => d.fst)
    (t := univ.filter (fun v => f v = x))]
  · apply sum_congr rfl
    intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    rw [← dart_fst_fiber_card_eq_degree]
    congr 1
    ext d
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro h; exact ⟨h ▸ hv, h⟩
  · intro d hd
    simpa using hd

theorem sum_degree_of_regular {d : ℕ} (hreg : G.IsRegularOfDegree d) (s : Finset V) :
    ∑ v ∈ s, G.degree v = d * s.card := by
  rw [sum_congr rfl fun v _ => hreg.degree_eq v]
  simp [mul_comm]

/-- Darts from colour `x` split by the colour of their head. -/
theorem card_darts_fst_color_eq_sum [Fintype W] (f : G →g H) (x : W) :
    (univ.filter fun d : G.Dart => f d.fst = x).card =
      ∑ y, (univ.filter fun d : G.Dart => f d.fst = x ∧ f d.snd = y).card := by
  rw [card_eq_sum_card_fiberwise (f := fun d : G.Dart => f d.snd) (t := univ)
    (fun _ _ => mem_univ _)]
  apply sum_congr rfl
  intro y _
  congr 1
  ext d
  simp

section Three

local notation "K3" => (⊤ : SimpleGraph (Fin 3))

variable (f : G →g K3)

/-- Size of colour class `i`. -/
def cls (i : Fin 3) : ℕ := (univ.filter fun v => f v = i).card

theorem cls_sum : cls f 0 + cls f 1 + cls f 2 = Fintype.card V := by
  classical
  have := card_eq_sum_card_fiberwise (f := f) (s := (univ : Finset V)) (t := univ)
    (fun _ _ => mem_univ _)
  rw [card_univ, Fin.sum_univ_three] at this
  rw [this]
  simp only [cls]
  all_goals rfl

theorem darts_same_color_empty (x : Fin 3) :
    (univ.filter fun d : G.Dart => f d.fst = x ∧ f d.snd = x).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro d - ⟨h1, h2⟩
  exact (f.map_rel d.adj) (h1.trans h2.symm)

theorem load_swap (x y : Fin 3) : load f s(x, y) = load f s(y, x) := by
  rw [Sym2.eq_swap]

/-- `d·a = L₀₁ + L₀₂`, etc. -/
theorem regular_class_eq {d : ℕ} (hreg : G.IsRegularOfDegree d) :
    d * cls f 0 = load f s(0, 1) + load f s(0, 2) ∧
    d * cls f 1 = load f s(0, 1) + load f s(1, 2) ∧
    d * cls f 2 = load f s(0, 2) + load f s(1, 2) := by
  have key : ∀ x : Fin 3, d * cls f x =
      ∑ y, (univ.filter fun d : G.Dart => f d.fst = x ∧ f d.snd = y).card := by
    intro x
    rw [← card_darts_fst_color_eq_sum, card_darts_fst_color, sum_degree_of_regular hreg]
    rfl
  have L : ∀ x y : Fin 3, x ≠ y →
      (univ.filter fun d : G.Dart => f d.fst = x ∧ f d.snd = y).card = load f s(x, y) :=
    fun x y h => (load_eq_card_darts f h).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [key, Fin.sum_univ_three, darts_same_color_empty, L 0 1 (by decide), L 0 2 (by decide)]
    ring
  · rw [key, Fin.sum_univ_three, darts_same_color_empty, L 1 0 (by decide), L 1 2 (by decide),
      load_swap f 1 0]
    ring
  · rw [key, Fin.sum_univ_three, darts_same_color_empty, L 2 0 (by decide), L 2 1 (by decide),
      load_swap f 2 0, load_swap f 2 1]
    ring

theorem map_edge_K3 {e : Sym2 V} (he : e ∈ G.edgeSet) :
    e.map f = s(0, 1) ∨ e.map f = s(0, 2) ∨ e.map f = s(1, 2) := by
  induction e using Sym2.ind with
  | _ u v =>
    have hne : f u ≠ f v := f.map_rel he
    rw [Sym2.map_mk]
    generalize f u = a at hne
    generalize f v = b at hne
    fin_cases a <;> fin_cases b <;> simp_all [Sym2.eq_swap]

/-- `μ(f) = max(L₀₁, L₀₂, L₁₂)`. -/
theorem mu_K3 : mu f = max (max (load f s(0, 1)) (load f s(0, 2))) (load f s(1, 2)) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro e he
    rw [mem_edgeFinset] at he
    rcases map_edge_K3 f he with h | h | h <;> rw [h] <;> simp
  · exact max_le (max_le (load_le_mu f _) (load_le_mu f _)) (load_le_mu f _)

/-- Degree sum of colour class `i`. -/
def degCls (i : Fin 3) : ℕ := ∑ v ∈ univ.filter (fun v => f v = i), G.degree v

/-- For any graph: `D₀ = L₀₁ + L₀₂`, `D₁ = L₀₁ + L₁₂`, `D₂ = L₀₂ + L₁₂`. -/
theorem degCls_eq :
    degCls f 0 = load f s(0, 1) + load f s(0, 2) ∧
    degCls f 1 = load f s(0, 1) + load f s(1, 2) ∧
    degCls f 2 = load f s(0, 2) + load f s(1, 2) := by
  have key : ∀ x : Fin 3, degCls f x =
      ∑ y, (univ.filter fun d : G.Dart => f d.fst = x ∧ f d.snd = y).card := by
    intro x
    rw [← card_darts_fst_color_eq_sum, card_darts_fst_color]
    rfl
  have L : ∀ x y : Fin 3, x ≠ y →
      (univ.filter fun d : G.Dart => f d.fst = x ∧ f d.snd = y).card = load f s(x, y) :=
    fun x y h => (load_eq_card_darts f h).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [key, Fin.sum_univ_three, darts_same_color_empty, L 0 1 (by decide), L 0 2 (by decide)]
    ring
  · rw [key, Fin.sum_univ_three, darts_same_color_empty, L 1 0 (by decide), L 1 2 (by decide),
      load_swap f 1 0]
    ring
  · rw [key, Fin.sum_univ_three, darts_same_color_empty, L 2 0 (by decide), L 2 1 (by decide),
      load_swap f 2 0, load_swap f 2 1]
    ring

/-- For distinct colours `a, b, c`: `2·L_{ab} = D_a + D_b - D_c`. -/
theorem two_load_eq (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (2 * load f s(a, b) : ℤ) = degCls f a + degCls f b - degCls f c := by
  obtain ⟨h0, h1, h2⟩ := degCls_eq f
  have s10 := load_swap f 1 0
  have s20 := load_swap f 2 0
  have s21 := load_swap f 2 1
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp at hab hac hbc ⊢ <;> push_cast [*] <;> ring

/-- The general (irregular) form of the d-regularity identity:
`2·μ(f) = max(D₀+D₁-D₂, D₀+D₂-D₁, D₁+D₂-D₀)` where `Dᵢ` is the degree sum of class `i`. -/
theorem two_mu_eq_deg :
    (2 * mu f : ℤ) = max (max ((degCls f 0 : ℤ) + degCls f 1 - degCls f 2)
      ((degCls f 0 : ℤ) + degCls f 2 - degCls f 1)) ((degCls f 1 : ℤ) + degCls f 2 - degCls f 0) := by
  rw [mu_K3, ← two_load_eq f 0 1 2 (by decide) (by decide) (by decide),
    ← two_load_eq f 0 2 1 (by decide) (by decide) (by decide),
    ← two_load_eq f 1 2 0 (by decide) (by decide) (by decide)]
  push_cast
  rw [← mul_max_of_nonneg _ _ (by norm_num), ← mul_max_of_nonneg _ _ (by norm_num)]

/-- **The d-regularity identity.** For `d`-regular `G` and any `f : G → K₃` with colour classes
of sizes `a, b, c`: `2·μ(f) = d·max(a+b-c, a+c-b, b+c-a)` (in `ℤ`). -/
theorem two_mu_eq {d : ℕ} (hreg : G.IsRegularOfDegree d) :
    (2 * mu f : ℤ) = d * max (max ((cls f 0 : ℤ) + cls f 1 - cls f 2)
      ((cls f 0 : ℤ) + cls f 2 - cls f 1)) ((cls f 1 : ℤ) + cls f 2 - cls f 0) := by
  obtain ⟨h0, h1, h2⟩ := regular_class_eq f hreg
  rw [mu_K3]
  have e1 : (d : ℤ) * ((cls f 0 : ℤ) + cls f 1 - cls f 2) = 2 * load f s(0, 1) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h0
    have := congrArg (fun n : ℕ => (n : ℤ)) h1
    have := congrArg (fun n : ℕ => (n : ℤ)) h2
    push_cast at *; linarith
  have e2 : (d : ℤ) * ((cls f 0 : ℤ) + cls f 2 - cls f 1) = 2 * load f s(0, 2) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h0
    have := congrArg (fun n : ℕ => (n : ℤ)) h1
    have := congrArg (fun n : ℕ => (n : ℤ)) h2
    push_cast at *; linarith
  have e3 : (d : ℤ) * ((cls f 1 : ℤ) + cls f 2 - cls f 0) = 2 * load f s(1, 2) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h0
    have := congrArg (fun n : ℕ => (n : ℤ)) h1
    have := congrArg (fun n : ℕ => (n : ℤ)) h2
    push_cast at *; linarith
  rw [mul_max_of_nonneg _ _ (by positivity), mul_max_of_nonneg _ _ (by positivity), e1, e2, e3]
  push_cast
  rw [← mul_max_of_nonneg _ _ (by norm_num), ← mul_max_of_nonneg _ _ (by norm_num)]

/-- The triple `(a+b-c, a+c-b, b+c-a)` is non-negative (for `d > 0`), sums to `|V|`, and has
constant parity. -/
theorem triple_props {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) :
    0 ≤ (cls f 0 : ℤ) + cls f 1 - cls f 2 ∧ 0 ≤ (cls f 0 : ℤ) + cls f 2 - cls f 1 ∧
    0 ≤ (cls f 1 : ℤ) + cls f 2 - cls f 0 ∧
    ((cls f 0 : ℤ) + cls f 1 - cls f 2) + ((cls f 0 : ℤ) + cls f 2 - cls f 1) +
      ((cls f 1 : ℤ) + cls f 2 - cls f 0) = Fintype.card V ∧
    ((cls f 0 : ℤ) + cls f 1 - cls f 2) % 2 = ((cls f 0 : ℤ) + cls f 2 - cls f 1) % 2 ∧
    ((cls f 0 : ℤ) + cls f 2 - cls f 1) % 2 = ((cls f 1 : ℤ) + cls f 2 - cls f 0) % 2 := by
  obtain ⟨h0, h1, h2⟩ := regular_class_eq f hreg
  have hs := cls_sum f
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have z0 := congrArg (fun n : ℕ => (n : ℤ)) h0
  have z1 := congrArg (fun n : ℕ => (n : ℤ)) h1
  have z2 := congrArg (fun n : ℕ => (n : ℤ)) h2
  push_cast at z0 z1 z2
  have p1 : 0 ≤ (d : ℤ) * ((cls f 0 : ℤ) + cls f 1 - cls f 2) := by nlinarith
  have p2 : 0 ≤ (d : ℤ) * ((cls f 0 : ℤ) + cls f 2 - cls f 1) := by nlinarith
  have p3 : 0 ≤ (d : ℤ) * ((cls f 1 : ℤ) + cls f 2 - cls f 0) := by nlinarith
  have hsz : ((cls f 0 : ℕ) : ℤ) + cls f 1 + cls f 2 = Fintype.card V := by exact_mod_cast hs
  refine ⟨(mul_nonneg_iff_of_pos_left hd').mp p1, (mul_nonneg_iff_of_pos_left hd').mp p2,
    (mul_nonneg_iff_of_pos_left hd').mp p3, by linarith, by omega, by omega⟩

/-- Per-homomorphism form of the lower bound in Theorem `thm:d_regular`: if every admissible
triple has some entry `≥ M`, then `d·M ≤ 2·μ(f)`. -/
theorem mu_lower {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) (M : ℕ)
    (hM : ∀ s₁ s₂ s₃ : ℤ, 0 ≤ s₁ → 0 ≤ s₂ → 0 ≤ s₃ → s₁ + s₂ + s₃ = Fintype.card V →
      s₁ % 2 = s₂ % 2 → s₂ % 2 = s₃ % 2 → (M : ℤ) ≤ s₁ ∨ (M : ℤ) ≤ s₂ ∨ (M : ℤ) ≤ s₃) :
    d * M ≤ 2 * mu f := by
  obtain ⟨p1, p2, p3, psum, q1, q2⟩ := triple_props f hd hreg
  have hmax : (M : ℤ) ≤ max (max ((cls f 0 : ℤ) + cls f 1 - cls f 2)
      ((cls f 0 : ℤ) + cls f 2 - cls f 1)) ((cls f 1 : ℤ) + cls f 2 - cls f 0) := by
    rcases hM _ _ _ p1 p2 p3 psum q1 q2 with h | h | h
    · exact h.trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact h.trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact h.trans (le_max_right _ _)
  have := two_mu_eq f hreg
  have : (d : ℤ) * M ≤ 2 * mu f := by
    rw [this]; exact mul_le_mul_of_nonneg_left hmax (by positivity)
  exact_mod_cast this

end Three

/-- **Theorem `thm:d_regular`, lower bound.** Let `G` be `d`-regular (`d > 0`). If `M` is a lower
bound for `max(s₁,s₂,s₃)` over all non-negative same-parity triples summing to `|V(G)|`, then
`d·M ≤ 2·γ(G,K₃)`, i.e. `γ(G,K₃) ≥ (d/2)·M`. -/
theorem gamma_K3_lower {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) (M : ℕ)
    (hM : ∀ s₁ s₂ s₃ : ℤ, 0 ≤ s₁ → 0 ≤ s₂ → 0 ≤ s₃ → s₁ + s₂ + s₃ = Fintype.card V →
      s₁ % 2 = s₂ % 2 → s₂ % 2 = s₃ % 2 → (M : ℤ) ≤ s₁ ∨ (M : ℤ) ≤ s₂ ∨ (M : ℤ) ≤ s₃) :
    ((d * M : ℕ) : ℕ∞) ≤ 2 * gamma G (⊤ : SimpleGraph (Fin 3)) := by
  by_cases h : Nonempty (G →g (⊤ : SimpleGraph (Fin 3)))
  · obtain ⟨f, hf⟩ := exists_gamma_eq h
    rw [← hf]
    exact_mod_cast mu_lower f hd hreg M hM
  · rw [not_nonempty_iff] at h
    rw [gamma_eq_top_iff.mpr h, ENat.mul_top (by norm_num)]
    exact le_top

/-- **Theorem `thm:d_regular`, equality criterion.** If some proper 3-colouring has class sizes
whose triple has maximum `M`, then `2·γ(G,K₃) ≤ d·M`. -/
theorem gamma_K3_upper {d : ℕ} (hreg : G.IsRegularOfDegree d)
    (f : G →g (⊤ : SimpleGraph (Fin 3))) (M : ℕ)
    (hf : max (max ((cls f 0 : ℤ) + cls f 1 - cls f 2) ((cls f 0 : ℤ) + cls f 2 - cls f 1))
      ((cls f 1 : ℤ) + cls f 2 - cls f 0) = M) :
    2 * gamma G (⊤ : SimpleGraph (Fin 3)) ≤ ((d * M : ℕ) : ℕ∞) := by
  have h2 := two_mu_eq f hreg
  rw [hf] at h2
  have : 2 * mu f = d * M := by exact_mod_cast h2
  calc 2 * gamma G (⊤ : SimpleGraph (Fin 3)) ≤ 2 * (mu f : ℕ∞) := by
        gcongr; exact gamma_le_mu f
    _ = ((d * M : ℕ) : ℕ∞) := by rw [← this]; push_cast; rfl

end NonHom
