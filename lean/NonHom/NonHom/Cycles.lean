import NonHom.Regular

/-!
# Cycles (Theorem `thm:cycle_gamma`)

`γ(C_n, K₃) = ⌈n/3⌉` if `n ≢ 2 (mod 3)` and `⌈n/3⌉ + 1` if `n ≡ 2 (mod 3)`, for all `n ≥ 3`.
Also `|C_n, K₃| = 0`, and `|C_n,K₂|` is `0` for even `n`.
-/

open SimpleGraph Finset

namespace NonHom

/-- The right-hand side of Theorem `thm:cycle_gamma` (`⌈n/3⌉ = (n+2)/3`). -/
def cycleGammaFormula (n : ℕ) : ℕ := if n % 3 = 2 then (n + 2) / 3 + 1 else (n + 2) / 3

theorem cycle_adj_val {k : ℕ} {u v : Fin (k + 3)} (h : (cycleGraph (k + 3)).Adj u v) :
    u.val = v.val + 1 ∨ v.val = u.val + 1 ∨ (u.val = 0 ∧ v.val = k + 2) ∨
      (v.val = 0 ∧ u.val = k + 2) := by
  rw [cycleGraph_adj'] at h
  have hu := u.isLt
  have hv := v.isLt
  rcases h with h | h
  · by_cases hle : v.val ≤ u.val
    · rw [Fin.coe_sub_iff_le.mpr (show v ≤ u from hle)] at h; omega
    · rw [Fin.coe_sub_iff_lt.mpr (show u < v by exact Nat.lt_of_not_le hle)] at h; omega
  · by_cases hle : u.val ≤ v.val
    · rw [Fin.coe_sub_iff_le.mpr (show u ≤ v from hle)] at h; omega
    · rw [Fin.coe_sub_iff_lt.mpr (show v < u by exact Nat.lt_of_not_le hle)] at h; omega

/-- Colour `i ↦ i mod 3` on the first `3⌊n/3⌋` vertices, then `0, 1` / `1` on the tail. -/
def cval (n i : ℕ) : ℕ := if i < 3 * (n / 3) then i % 3 else if i + 1 = n then 1 else 0

theorem cval_lt (n i : ℕ) : cval n i < 3 := by
  unfold cval; split_ifs <;> omega

/-- The explicit optimal homomorphism `C_n → K₃`. -/
def cycleColoring (k : ℕ) : cycleGraph (k + 3) →g (⊤ : SimpleGraph (Fin 3)) where
  toFun i := ⟨cval (k + 3) i.val, cval_lt _ _⟩
  map_rel' := by
    intro u v h
    have := cycle_adj_val h
    have hu := u.isLt
    have hv := v.isLt
    simp only [top_adj, ne_eq, Fin.mk.injEq]
    unfold cval
    split_ifs <;> first | omega | exact not_false

theorem sum_mod_three (q j : ℕ) (hj : j < 3) :
    ∑ x ∈ range (3 * q), (if x % 3 = j then 1 else 0) = q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 3 * (q + 1) = 3 * q + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_succ, ih]
    split_ifs <;> omega

theorem count_cval (n j : ℕ) (hj : j < 3) :
    ∑ x ∈ range n, (if cval n x = j then 1 else 0) = n / 3 +
      (if n % 3 = 2 ∧ j = 0 then 1 else 0) + (if n % 3 ≠ 0 ∧ j = 1 then 1 else 0) := by
  have head : ∀ q r, r < 3 → ∑ x ∈ range (3 * q), (if cval (3 * q + r) x = j then 1 else 0) = q := by
    intro q r hr
    refine (sum_congr rfl ?_).trans (sum_mod_three q j hj)
    intro x hx
    rw [mem_range] at hx
    have : cval (3 * q + r) x = x % 3 := by
      unfold cval
      rw [ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]
    rw [this]
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
  · obtain ⟨q, rfl⟩ : ∃ q, n = 3 * q + 0 := ⟨n / 3, by omega⟩
    rw [sum_range_add, head q 0 (by norm_num)]
    simp only [sum_range_zero]
    split_ifs <;> omega
  · obtain ⟨q, rfl⟩ : ∃ q, n = 3 * q + 1 := ⟨n / 3, by omega⟩
    rw [sum_range_add, head q 1 (by norm_num), sum_range_one]
    simp only [cval]
    split_ifs <;> omega
  · obtain ⟨q, rfl⟩ : ∃ q, n = 3 * q + 2 := ⟨n / 3, by omega⟩
    rw [sum_range_add, head q 2 (by norm_num), sum_range_succ, sum_range_one]
    simp only [cval]
    split_ifs <;> omega

theorem cls_cycleColoring_eq (k : ℕ) (j : Fin 3) :
    cls (cycleColoring k) j = (k + 3) / 3 +
      (if (k + 3) % 3 = 2 ∧ j.val = 0 then 1 else 0) +
      (if (k + 3) % 3 ≠ 0 ∧ j.val = 1 then 1 else 0) := by
  rw [← count_cval (k + 3) j.val j.isLt]
  unfold cls
  rw [card_filter, ← Fin.sum_univ_eq_sum_range (fun x => if cval (k + 3) x = j.val then 1 else 0)]
  apply sum_congr rfl
  intro i _
  have : (cycleColoring k i = j) ↔ cval (k + 3) i.val = j.val := Fin.ext_iff
  simp only [this]

theorem cycleGraph_regular (k : ℕ) : (cycleGraph (k + 3)).IsRegularOfDegree 2 :=
  fun _ => cycleGraph_degree_three_le

/-- **Theorem `thm:cycle_gamma`.** -/
theorem gamma_cycle (n : ℕ) (hn : 3 ≤ n) :
    gamma (cycleGraph n) (⊤ : SimpleGraph (Fin 3)) = cycleGammaFormula n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  apply le_antisymm
  · -- upper bound: the explicit colouring
    refine (gamma_le_mu (cycleColoring k)).trans ?_
    have h2 := two_mu_eq (cycleColoring k) (cycleGraph_regular k)
    rw [cls_cycleColoring_eq, cls_cycleColoring_eq, cls_cycleColoring_eq] at h2
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at h2
    have : mu (cycleColoring k) ≤ cycleGammaFormula (k + 3) := by
      unfold cycleGammaFormula
      rcases (by omega : (k + 3) % 3 = 0 ∨ (k + 3) % 3 = 1 ∨ (k + 3) % 3 = 2) with hr | hr | hr <;>
      · simp only [hr, max_def] at h2 ⊢
        norm_num at h2 ⊢
        first | omega | (split_ifs at h2 <;> omega)
    exact_mod_cast this
  · -- lower bound: the parity argument
    apply le_gamma
    intro f
    have := mu_lower f (by norm_num) (cycleGraph_regular k) (cycleGammaFormula (k + 3)) (by
      intro s₁ s₂ s₃ h1 h2 h3 hs p1 p2
      simp only [Fintype.card_fin] at hs
      unfold cycleGammaFormula
      split_ifs <;> push_cast <;> omega)
    exact_mod_cast (by omega : cycleGammaFormula (k + 3) ≤ mu f)

/-- `|C_n,K₃| = 0`: every cycle is 3-colourable. -/
theorem nhf_cycle_K3 (n : ℕ) (hn : 2 ≤ n) :
    nhf (cycleGraph n) (⊤ : SimpleGraph (Fin 3)) = 0 :=
  nhf_eq_zero_of_hom (cycleGraph.tricoloring n hn)

/-- `|C_n,K₂| = 0` for even `n`. -/
theorem nhf_cycle_K2_even (n : ℕ) (h : Even n) :
    nhf (cycleGraph n) (⊤ : SimpleGraph Bool) = 0 :=
  nhf_eq_zero_of_hom (cycleGraph.bicoloring_of_even n h)

end NonHom
