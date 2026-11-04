import NonHom.Gamma

/-!
# The averaging upper bound

**Theorem.** For all finite `G`, `H` with `V(H) ≠ ∅`,
`|V(H)|²·|G,H| ≤ |E(G)|·(|V(H)|² - 2|E(H)|)`; equivalently a uniformly random map
`V(G) → V(H)` keeps each edge with probability `2|E(H)|/|V(H)|²`.
For `H = K_m` this is `|G,K_m| ≤ |E(G)|/m`.
-/

open SimpleGraph Finset

namespace NonHom

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Summing a function of two coordinates over all maps `V → W`. -/
theorem sum_fun_two {u v : V} (huv : u ≠ v) :
    ∃ C : ℕ, ∀ g : W → W → ℕ, ∑ f : V → W, g (f u) (f v) = C * ∑ a, ∑ b, g a b := by
  classical
  let v' : {j // j ≠ u} := ⟨v, huv.symm⟩
  refine ⟨Fintype.card ({j' : {j // j ≠ u} // j' ≠ v'} → W), fun g => ?_⟩
  rw [← Fintype.sum_equiv (Equiv.piSplitAt u (fun _ => W)).symm
    (fun p => g p.1 (p.2 v')) (fun f => g (f u) (f v)) (fun p => by
      simp [Equiv.piSplitAt, v', huv.symm])]
  rw [Fintype.sum_prod_type, mul_sum]
  apply sum_congr rfl
  intro a _
  rw [← Fintype.sum_equiv (Equiv.piSplitAt v' (fun _ => W)).symm
    (fun p => g a p.1) (fun r => g a (r v')) (fun p => by simp [Equiv.piSplitAt])]
  rw [Fintype.sum_prod_type, mul_sum]
  apply sum_congr rfl
  intro b _
  simp [mul_comm]

/-- **Averaging bound.** `|V(H)|²·|G,H| ≤ |E(G)|·(|V(H)|² - 2|E(H)|)`. -/
theorem nhf_average {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W}
    [DecidableRel H.Adj] [Nonempty W] :
    nhf G H * (Fintype.card W ^ 2 : ℕ) ≤
      ((G.edgeFinset.card * (Fintype.card W ^ 2 - 2 * H.edgeFinset.card) : ℕ) : ℕ∞) := by
  classical
  -- bad edges of a map
  let bad : (V → W) → Finset (Sym2 V) := fun f =>
    G.edgeFinset.filter fun e => e.map f ∉ H.edgeSet
  have hbad : ∀ f, nhf G H ≤ (bad f).card := by
    intro f
    apply nhf_le_card
    refine ⟨⟨f, fun {a b} h => ?_⟩⟩
    rw [deleteEdges_adj] at h
    by_contra hn
    apply h.2
    simp only [bad, coe_filter, mem_edgeFinset, Set.mem_ofPred_eq]
    exact ⟨h.1, hn⟩
  -- number of non-adjacent ordered pairs
  set N := (univ.filter fun p : W × W => ¬ H.Adj p.1 p.2).card
  have hN : N = Fintype.card W ^ 2 - 2 * H.edgeFinset.card := by
    have h1 := card_filter_add_card_filter_not (s := (univ : Finset (W × W))) (fun p => H.Adj p.1 p.2)
    rw [card_univ, Fintype.card_prod, ← two_mul_card_edgeFinset] at h1
    rw [sq]; omega
  by_cases hE : G.edgeFinset = ∅
  · have : nhf G H = 0 := by
      have := hbad (fun _ => Classical.arbitrary W)
      simp only [bad, hE, filter_empty, card_empty, Nat.cast_zero, nonpos_iff_eq_zero] at this
      exact this
    rw [this, zero_mul]; exact zero_le
  obtain ⟨e₀, he₀⟩ := nonempty_iff_ne_empty.mpr hE
  -- total badness over all maps
  have htot : ∀ e ∈ G.edgeFinset, ∃ C, (∑ f : V → W, if e.map f ∉ H.edgeSet then 1 else 0) = C * N ∧
      (Fintype.card W) ^ (Fintype.card V) = C * Fintype.card W ^ 2 := by
    intro e he
    rw [mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨C, hC⟩ := sum_fun_two (W := W) he.ne
      refine ⟨C, ?_, ?_⟩
      · have := hC (fun a b => if ¬ H.Adj a b then 1 else 0)
        simp only [Sym2.map_mk, mem_edgeSet] at this ⊢
        rw [this]
        congr 1
        simp only [N]
        rw [card_filter, Fintype.sum_prod_type]
      · have := hC (fun _ _ => 1)
        simp only [sum_const, card_univ, smul_eq_mul, mul_one, Fintype.card_fun] at this
        rw [this, sq]
  obtain ⟨C, -, hC⟩ := htot e₀ he₀
  have hCpos : 0 < C := by
    rcases Nat.eq_zero_or_pos C with h | h
    · rw [h, zero_mul] at hC
      exact absurd hC (pow_ne_zero _ Fintype.card_ne_zero)
    · exact h
  have hsum : ∑ f : V → W, (bad f).card = G.edgeFinset.card * (C * N) := by
    simp only [bad, card_filter]
    rw [sum_comm]
    rw [sum_congr rfl (fun e he => by
      obtain ⟨C', h1, h2⟩ := htot e he
      have : C' = C := by
        have := h2.symm.trans hC
        exact Nat.eq_of_mul_eq_mul_right (pow_pos Fintype.card_pos 2) this
      rw [h1, this])]
    simp
  -- choose a map with at most average badness
  obtain ⟨f, -, hf⟩ := exists_min_image (univ : Finset (V → W)) (fun f => (bad f).card) univ_nonempty
  have hmin : Fintype.card W ^ Fintype.card V * (bad f).card ≤ G.edgeFinset.card * (C * N) := by
    rw [← hsum, ← Fintype.card_fun, ← card_univ, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun g _ => hf g (mem_univ g)
  rw [hC] at hmin
  have key : (bad f).card * Fintype.card W ^ 2 ≤ G.edgeFinset.card * N := by
    have : C * ((bad f).card * Fintype.card W ^ 2) ≤ C * (G.edgeFinset.card * N) := by
      calc C * ((bad f).card * Fintype.card W ^ 2) = C * Fintype.card W ^ 2 * (bad f).card := by ring
        _ ≤ G.edgeFinset.card * (C * N) := hmin
        _ = C * (G.edgeFinset.card * N) := by ring
    exact Nat.le_of_mul_le_mul_left this hCpos
  rw [← hN]
  calc nhf G H * (Fintype.card W ^ 2 : ℕ) ≤ ((bad f).card : ℕ∞) * (Fintype.card W ^ 2 : ℕ) := by
        gcongr; exact hbad f
    _ ≤ _ := by exact_mod_cast key

end NonHom
