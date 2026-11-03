import NonHom.Regular

/-!
# Complete bipartite graphs (Theorem `thm:Knn`)

`γ(K_{n,n}, K₃) = n·⌈n/2⌉` and `|K_{n,n},K₃| = 0`.
-/

open SimpleGraph Finset

namespace NonHom

local notation "Knn" n => completeBipartiteGraph (Fin n) (Fin n)
local notation "K3" => (⊤ : SimpleGraph (Fin 3))

instance knnDec (n : ℕ) : DecidableRel (Knn n).Adj := fun a b =>
  inferInstanceAs (Decidable (_ ∨ _))

theorem knn_regular (n : ℕ) : (Knn n).IsRegularOfDegree n := by
  intro v
  rw [← card_neighborFinset_eq_degree]
  cases v with
  | inl a =>
    have : (Knn n).neighborFinset (Sum.inl a) = univ.map Function.Embedding.inr := by
      ext w; cases w <;> simp
    rw [this, card_map, card_univ, Fintype.card_fin]
  | inr a =>
    have : (Knn n).neighborFinset (Sum.inr a) = univ.map Function.Embedding.inl := by
      ext w; cases w <;> simp
    rw [this, card_map, card_univ, Fintype.card_fin]

/-- A 2-colouring of `K_{n,n}` (left ↦ 0, right ↦ 1), giving `|K_{n,n},K₃| = 0`. -/
def knnTwoColoring (n : ℕ) : (Knn n) →g K3 where
  toFun v := Sum.elim (fun _ => 0) (fun _ => 1) v
  map_rel' := by
    rintro (a | a) (b | b) h <;> simp_all

theorem nhf_knn_K3 (n : ℕ) : nhf (Knn n) K3 = 0 := nhf_eq_zero_of_hom (knnTwoColoring n)

theorem third_color (x y : Fin 3) (h : x ≠ y) :
    ∃ c : Fin 3, ∀ z : Fin 3, z ≠ x → z ≠ y → z = c := by
  revert x y; decide

/-- In any `f : K_{n,n} → K₃` (`n ≥ 1`) some colour class is exactly one side, so has size `n`. -/
theorem exists_cls_eq (n : ℕ) (hn : 0 < n) (f : (Knn n) →g K3) : ∃ c, cls f c = n := by
  have adj : ∀ a b : Fin n, f (Sum.inl a) ≠ f (Sum.inr b) := fun a b =>
    f.map_rel (by simp)
  by_cases h : ∃ a₁ a₂ : Fin n, f (Sum.inl a₁) ≠ f (Sum.inl a₂)
  · obtain ⟨a₁, a₂, h12⟩ := h
    obtain ⟨c, hc⟩ := third_color _ _ h12
    have hr : ∀ b, f (Sum.inr b) = c := fun b =>
      hc _ (fun e => adj a₁ b e.symm) (fun e => adj a₂ b e.symm)
    refine ⟨c, ?_⟩
    have : (univ.filter fun v => f v = c) = univ.map Function.Embedding.inr := by
      ext v
      cases v with
      | inl a => simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.inr_apply,
          reduceCtorEq, and_false, exists_false, iff_false]
                 intro e; exact adj a ⟨0, hn⟩ (e.trans (hr _).symm)
      | inr b => simp [hr b]
    rw [cls, this, card_map, card_univ, Fintype.card_fin]
  · push Not at h
    refine ⟨f (Sum.inl ⟨0, hn⟩), ?_⟩
    have : (univ.filter fun v => f v = f (Sum.inl ⟨0, hn⟩)) = univ.map Function.Embedding.inl := by
      ext v
      cases v with
      | inl a => simp [h a ⟨0, hn⟩]
      | inr b => simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.inl_apply,
          reduceCtorEq, and_false, exists_false, iff_false]
                 intro e; exact adj ⟨0, hn⟩ b e.symm
    rw [cls, this, card_map, card_univ, Fintype.card_fin]

/-- The optimal colouring: left side split `⌊n/2⌋ / ⌈n/2⌉` between colours 0, 1; right ↦ 2. -/
def knnColoring (n : ℕ) : (Knn n) →g K3 where
  toFun v := Sum.elim (fun a : Fin n => if a.val < n / 2 then 0 else 1) (fun _ => 2) v
  map_rel' := by
    rintro (a | a) (b | b) h <;> simp_all <;> split_ifs <;> decide

theorem sum_lt_count (n k : ℕ) : ∑ x ∈ range n, (if x < k then 1 else 0) = min n k := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; split_ifs <;> omega

theorem cls_knnColoring (n : ℕ) :
    cls (knnColoring n) 0 = n / 2 ∧ cls (knnColoring n) 1 = n - n / 2 ∧
      cls (knnColoring n) 2 = n := by
  have base : ∀ j : Fin 3, cls (knnColoring n) j =
      (∑ x ∈ range n, if (if x < n / 2 then (0 : Fin 3) else 1) = j then 1 else 0) +
        if (2 : Fin 3) = j then n else 0 := by
    intro j
    rw [cls, card_filter, Fintype.sum_sum_type]
    congr 1
    · rw [← Fin.sum_univ_eq_sum_range (fun x => if (if x < n / 2 then (0 : Fin 3) else 1) = j then 1 else 0)]
      rfl
    · by_cases h : (2 : Fin 3) = j
      · subst h; simp [knnColoring]
      · simp [knnColoring, h]
  refine ⟨?_, ?_, ?_⟩
  · rw [base]
    simp only [show ((2 : Fin 3) = 0) = False by decide, ite_false, add_zero]
    refine (sum_congr rfl ?_).trans ((sum_lt_count n (n / 2)).trans (by omega))
    intro x _; split_ifs <;> simp_all
  · rw [base]
    simp only [show ((2 : Fin 3) = 1) = False by decide, ite_false, add_zero]
    have : ∑ x ∈ range n, (if (if x < n / 2 then (0 : Fin 3) else 1) = 1 then 1 else 0) =
        n - ∑ x ∈ range n, (if x < n / 2 then 1 else 0) := by
      have hsum : ∀ m, ∑ x ∈ range m, (if (if x < n / 2 then (0 : Fin 3) else 1) = 1 then 1 else 0) +
          ∑ x ∈ range m, (if x < n / 2 then 1 else 0) = m := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [sum_range_succ, sum_range_succ]
          split_ifs <;> simp_all <;> omega
      have := hsum n
      omega
    rw [this, sum_lt_count]; omega
  · rw [base]
    simp only [ite_true]
    have : ∑ x ∈ range n, (if (if x < n / 2 then (0 : Fin 3) else 1) = 2 then 1 else 0) = 0 := by
      apply sum_eq_zero; intro x _; split_ifs <;> simp_all
    rw [this]; simp

/-- **Theorem `thm:Knn`**: `γ(K_{n,n}, K₃) = n·⌈n/2⌉`. -/
theorem gamma_knn (n : ℕ) : gamma (Knn n) K3 = ((n * ((n + 1) / 2) : ℕ) : ℕ∞) := by
  apply le_antisymm
  · refine (gamma_le_mu (knnColoring n)).trans ?_
    have h2 := two_mu_eq (knnColoring n) (knn_regular n)
    obtain ⟨c0, c1, c2⟩ := cls_knnColoring n
    rw [c0, c1, c2] at h2
    have hb : (n - n / 2 : ℕ) = (n + 1) / 2 := by omega
    rw [hb] at h2
    have hmax : max (max (((n / 2 : ℕ) : ℤ) + ((n + 1) / 2 : ℕ) - n)
        (((n / 2 : ℕ) : ℤ) + n - ((n + 1) / 2 : ℕ))) ((((n + 1) / 2 : ℕ) : ℤ) + n - (n / 2 : ℕ)) =
        2 * (((n + 1) / 2 : ℕ) : ℤ) := by
      simp only [max_def]; split_ifs <;> omega
    rw [hmax] at h2
    have : (mu (knnColoring n) : ℤ) = n * (((n + 1) / 2 : ℕ) : ℤ) := by linarith
    exact_mod_cast this.le
  · apply le_gamma
    intro f
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    obtain ⟨c, hc⟩ := exists_cls_eq n hn f
    have h2 := two_mu_eq f (knn_regular n)
    have hs := cls_sum f
    simp only [Fintype.card_sum, Fintype.card_fin] at hs
    have hM : 2 * (((n + 1) / 2 : ℕ) : ℤ) ≤ max (max ((cls f 0 : ℤ) + cls f 1 - cls f 2)
        ((cls f 0 : ℤ) + cls f 2 - cls f 1)) ((cls f 1 : ℤ) + cls f 2 - cls f 0) := by
      fin_cases c <;> simp at hc <;> simp only [max_def] <;> split_ifs <;> omega
    have : (n : ℤ) * (2 * (((n + 1) / 2 : ℕ) : ℤ)) ≤ 2 * mu f := by
      rw [h2]; exact mul_le_mul_of_nonneg_left hM (by positivity)
    have : ((n * ((n + 1) / 2) : ℕ) : ℤ) ≤ mu f := by rw [Nat.cast_mul]; linarith
    exact_mod_cast this

/-- Table `tab:KnnK3`: `γ(K_{n,n},K₃) = 1, 2, 6, 8` for `n = 1, 2, 3, 4`. -/
theorem table_KnnK3 : (List.range 4).map (fun i => (i + 1) * ((i + 2) / 2)) = [1, 2, 6, 8] := by
  decide

end NonHom
