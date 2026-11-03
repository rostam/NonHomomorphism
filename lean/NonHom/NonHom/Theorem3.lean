import NonHom.OpenProblems

/-!
# Theorem 3 of `open_problems/README.md`: `|C_p × C_q, K₂| = 2p` for odd `3 ≤ p ≤ q`

Lower bound: the `2pq` closed walks `i ↦ (a + σ·G(i), h + i)` (`a ∈ ℤ_p`, `h ∈ ℤ_q`, `σ = ±1`),
where `G` takes `(q+p)/2` steps `+1` then `(q-p)/2` steps `-1`, are odd closed walks of length `q`,
so each contains a deleted edge; and every edge is used by at most `q` of them at a fixed step
index, giving `2pq ≤ q·|S|`.
-/

open SimpleGraph Finset
open Fin.NatCast Fin.CommRing

namespace NonHom

variable (k l : ℕ)

local notation "P" => k + 3
local notation "Q" => l + 3

/-- Step `i` of the first coordinate. -/
def eps (i : ℕ) : Fin P := if i < (Q + P) / 2 then 1 else -1

/-- Partial sums. -/
def Gs (i : ℕ) : Fin P := ∑ j ∈ range i, eps k l j

def sgn (b : Bool) : Fin P := if b then 1 else -1

/-- The walk vertex. -/
def wv (a : Fin P) (h : Fin Q) (b : Bool) (i : ℕ) : Fin P × Fin Q :=
  (a + sgn k b * Gs k l i, h + (i : Fin Q))

theorem two_ne_zero_fin (n : ℕ) : (2 : Fin (n + 3)) ≠ 0 := by
  rw [ne_eq, Fin.ext_iff]
  simp only [Fin.val_zero]
  show 2 % (n + 3) ≠ 0
  rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem one_ne_neg_one_fin (n : ℕ) : (1 : Fin (n + 3)) ≠ -1 := by
  intro h
  apply two_ne_zero_fin n
  calc (2 : Fin (n + 3)) = 1 + 1 := by ring
    _ = -1 + 1 := by rw [← h]
    _ = 0 := by ring

theorem eps_sq (i : ℕ) : eps k l i * eps k l i = 1 := by
  unfold eps; split_ifs <;> ring

theorem sgn_sq (b : Bool) : sgn k b * sgn k b = 1 := by
  unfold sgn; split_ifs <;> ring

theorem Gs_succ (i : ℕ) : Gs k l (i + 1) = Gs k l i + eps k l i := by
  simp [Gs, sum_range_succ]

theorem Gs_Q (hP : Odd P) (hQ : Odd Q) (hPQ : P ≤ Q) : Gs k l Q = 0 := by
  obtain ⟨A, B, hAB, hA, hAdef⟩ : ∃ A B : ℕ, A + B = Q ∧ A = B + P ∧ A = (Q + P) / 2 := by
    obtain ⟨x, hx⟩ := hP; obtain ⟨y, hy⟩ := hQ
    exact ⟨(Q + P) / 2, (Q - P) / 2, by omega, by omega, rfl⟩
  rw [← hAB]
  unfold Gs
  rw [sum_range_add]
  have h1 : ∑ x ∈ range A, eps k l x = (A : Fin P) := by
    calc ∑ x ∈ range A, eps k l x = ∑ _x ∈ range A, (1 : Fin P) := by
          apply sum_congr rfl
          intro x hx
          rw [mem_range] at hx
          simp only [eps]
          rw [if_pos (by omega)]
      _ = A := by rw [sum_const, card_range, nsmul_eq_mul, mul_one]
  have h2 : ∑ x ∈ range B, eps k l (A + x) = -(B : Fin P) := by
    calc ∑ x ∈ range B, eps k l (A + x) = ∑ _x ∈ range B, (-1 : Fin P) := by
          apply sum_congr rfl
          intro x _
          simp only [eps]
          rw [if_neg (by omega)]
      _ = -(B : Fin P) := by rw [sum_const, card_range, nsmul_eq_mul, mul_neg, mul_one]
  rw [h1, h2, hA, Nat.cast_add, show ((k + 3 : ℕ) : Fin (k + 3)) = 0 from Fin.natCast_self (k + 3)]
  ring

theorem wv_adj (a : Fin P) (h : Fin Q) (b : Bool) (i : ℕ) :
    (tensor (cycleGraph P) (cycleGraph Q)).Adj (wv k l a h b i) (wv k l a h b (i + 1)) := by
  refine ⟨?_, ?_⟩
  · show (cycleGraph (k + 1 + 2)).Adj _ _
    rw [cycleGraph_adj]
    simp only [wv, Gs_succ]
    unfold sgn eps
    split_ifs
    · right; ring
    · left; ring
    · left; ring
    · right; ring
  · show (cycleGraph (l + 1 + 2)).Adj _ _
    rw [cycleGraph_adj]
    right
    simp only [wv]
    push_cast
    ring

theorem wv_closed (hP : Odd P) (hQ : Odd Q) (hPQ : P ≤ Q) (a : Fin P) (h : Fin Q) (b : Bool) :
    wv k l a h b Q = wv k l a h b 0 := by
  simp only [wv]
  rw [Gs_Q k l hP hQ hPQ, show ((l + 3 : ℕ) : Fin (l + 3)) = 0 from Fin.natCast_self (l + 3)]
  simp [Gs]

theorem fin2_ne (x y : Fin 2) (h : x ≠ y) : x = y + 1 := by
  revert x y; decide

/-- Every walk of the family meets every deletion set that makes the product bipartite. -/
theorem walk_meets (hP : Odd P) (hQ : Odd Q) (hPQ : P ≤ Q) (S : Finset (Sym2 (Fin P × Fin Q)))
    (g : (tensor (cycleGraph P) (cycleGraph Q)).deleteEdges ↑S →g (⊤ : SimpleGraph (Fin 2)))
    (a : Fin P) (h : Fin Q) (b : Bool) :
    ∃ i : Fin Q, s(wv k l a h b i, wv k l a h b (i + 1)) ∈ S := by
  by_contra hcon
  push Not at hcon
  have step : ∀ i < Q, g (wv k l a h b (i + 1)) = g (wv k l a h b i) + 1 := by
    intro i hi
    apply fin2_ne
    apply Ne.symm
    apply g.map_rel
    rw [deleteEdges_adj]
    exact ⟨wv_adj k l a h b i, hcon ⟨i, hi⟩⟩
  have par : ∀ i ≤ Q, g (wv k l a h b i) = g (wv k l a h b 0) + (i : Fin 2) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      rw [step i (by omega), ih (by omega)]
      push_cast; ring
  have := par Q le_rfl
  rw [wv_closed k l hP hQ hPQ] at this
  have hq2 : ((Q : ℕ) : Fin 2) = 1 := by
    obtain ⟨y, hy⟩ := hQ
    rw [hy]; push_cast
    simp
  rw [hq2] at this
  revert this
  generalize g (wv k l a h b 0) = x
  revert x; decide

/-- At a fixed step index, an edge is used by at most one walk of the family. -/
theorem walk_inj (a₁ a₂ : Fin P) (h₁ h₂ : Fin Q) (b₁ b₂ : Bool) (i : ℕ)
    (he : s(wv k l a₁ h₁ b₁ i, wv k l a₁ h₁ b₁ (i + 1)) = s(wv k l a₂ h₂ b₂ i, wv k l a₂ h₂ b₂ (i + 1))) :
    a₁ = a₂ ∧ h₁ = h₂ ∧ b₁ = b₂ := by
  rw [Sym2.eq_iff] at he
  simp only [wv, Prod.mk.injEq, Gs_succ] at he
  rcases he with ⟨⟨e1, e2⟩, ⟨e3, e4⟩⟩ | ⟨⟨e1, e2⟩, ⟨e3, e4⟩⟩
  · have hh : h₁ = h₂ := by simpa using e2
    have hs : sgn k b₁ * eps k l i = sgn k b₂ * eps k l i := by linear_combination e3 - e1
    have hs' : sgn k b₁ = sgn k b₂ := by
      have := congrArg (· * eps k l i) hs
      simp only [mul_assoc, eps_sq, mul_one] at this
      exact this
    have hb : b₁ = b₂ := by
      cases b₁ <;> cases b₂ <;> simp [sgn] at hs' <;> first | rfl | exact absurd hs'.symm (one_ne_neg_one_fin k) | exact absurd hs' (one_ne_neg_one_fin k)
    subst hb
    refine ⟨?_, hh, rfl⟩
    linear_combination e1
  · exfalso
    apply two_ne_zero_fin l
    push_cast at e2 e4
    linear_combination e4 - e2

/-- **Theorem 3, lower bound**: `|C_p × C_q, K₂| ≥ 2p` for odd `3 ≤ p ≤ q`. -/
theorem nhf_tensor_cycles_ge (hP : Odd P) (hQ : Odd Q) (hPQ : P ≤ Q) :
    ((2 * P : ℕ) : ℕ∞) ≤ nhf (tensor (cycleGraph P) (cycleGraph Q)) (⊤ : SimpleGraph (Fin 2)) := by
  apply le_nhf
  intro S ⟨g⟩
  have hm := fun (ω : Fin P × Fin Q × Bool) => walk_meets k l hP hQ hPQ S g ω.1 ω.2.1 ω.2.2
  choose idx hidx using hm
  let E : Fin P × Fin Q × Bool → Sym2 (Fin P × Fin Q) := fun ω =>
    s(wv k l ω.1 ω.2.1 ω.2.2 (idx ω), wv k l ω.1 ω.2.1 ω.2.2 (idx ω + 1))
  have hfib : ∀ e ∈ (univ : Finset (Fin P × Fin Q × Bool)).image E,
      ((univ : Finset (Fin P × Fin Q × Bool)).filter fun ω => E ω = e).card ≤ Q := by
    intro e _
    calc _ ≤ (univ : Finset (Fin Q)).card := by
          apply card_le_card_of_injOn idx (fun _ _ => mem_coe.mpr (mem_univ _))
          intro ω₁ h₁ ω₂ h₂ hi
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h₁ h₂
          have := h₁.trans h₂.symm
          simp only [E, hi] at this
          obtain ⟨ha, hh, hb⟩ := walk_inj k l _ _ _ _ _ _ _ this
          exact Prod.ext ha (Prod.ext hh hb)
      _ = Q := by simp
  have hcard := card_le_mul_card_image (univ : Finset (Fin P × Fin Q × Bool)) Q hfib
  have himg : ((univ : Finset (Fin P × Fin Q × Bool)).image E).card ≤ S.card :=
    card_le_card (fun e he => by
      obtain ⟨ω, -, rfl⟩ := mem_image.mp he
      exact hidx ω)
  simp only [card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hcard
  have : P * (Q * 2) ≤ Q * S.card := hcard.trans (Nat.mul_le_mul_left _ himg)
  have : 2 * P ≤ S.card := by
    by_contra hlt
    push Not at hlt
    have : Q * S.card < Q * (2 * P) := Nat.mul_lt_mul_of_pos_left hlt (by omega)
    nlinarith
  exact_mod_cast this

/-- **Theorem 3** of `open_problems/README.md`: `|C_p × C_q, K₂| = 2p` for odd `3 ≤ p ≤ q`. -/
theorem nhf_tensor_cycles (hP : Odd P) (hQ : Odd Q) (hPQ : P ≤ Q) :
    nhf (tensor (cycleGraph P) (cycleGraph Q)) (⊤ : SimpleGraph (Fin 2)) = ((2 * P : ℕ) : ℕ∞) :=
  le_antisymm (nhf_tensor_cycles_le k l hQ) (nhf_tensor_cycles_ge k l hP hQ hPQ)

end NonHom
