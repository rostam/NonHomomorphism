import NonHom.Theorem3
import NonHom.CycleCycle

/-!
# Products of odd cycles into arbitrary targets

**Theorem.** Let `3 ≤ p ≤ q` be odd and let `H` have an edge. Then
`|C_p × C_q, H| = 2p` if `C_q ↛ H`, and `= 0` if `C_q → H`.
In particular `|C_p × C_q, C_m| = 2p` for odd `p ≤ q < m`.
-/

open SimpleGraph Finset
open Fin.NatCast Fin.CommRing

namespace NonHom

variable (k l : ℕ) {W : Type*}

local notation "P" => k + 3
local notation "Q" => l + 3

/-- Every walk of the family meets `S` whenever `C_q ↛ H`. -/
theorem walk_meets_gen (hP : Odd P) (hQ : Odd Q) (hPQ : P ≤ Q) {H : SimpleGraph W}
    (hH : IsEmpty (cycleGraph Q →g H)) (S : Finset (Sym2 (Fin P × Fin Q)))
    (g : (tensor (cycleGraph P) (cycleGraph Q)).deleteEdges ↑S →g H)
    (a : Fin P) (h : Fin Q) (b : Bool) :
    ∃ i : Fin Q, s(wv k l a h b i, wv k l a h b (i + 1)) ∈ S := by
  by_contra hcon
  push Not at hcon
  have hsucc : ∀ u : Fin Q, wv k l a h b ((u + 1 : Fin Q) : ℕ) = wv k l a h b ((u : ℕ) + 1) := by
    intro u
    rw [Fin.val_add_one]
    split_ifs with hu
    · rw [hu, Fin.val_last]; exact (wv_closed k l hP hQ hPQ a h b).symm
    · rfl
  have step : ∀ u : Fin Q, ((tensor (cycleGraph P) (cycleGraph Q)).deleteEdges ↑S).Adj
      (wv k l a h b u) (wv k l a h b ((u + 1 : Fin Q) : ℕ)) := by
    intro u
    rw [hsucc, deleteEdges_adj]
    exact ⟨wv_adj k l a h b u, hcon u⟩
  let φ : cycleGraph Q →g (tensor (cycleGraph P) (cycleGraph Q)).deleteEdges ↑S :=
    ⟨fun u => wv k l a h b u, by
      intro u v huv
      rcases (cyc_adj_iff u v).mp huv with rfl | rfl
      · exact step u
      · exact (step v).symm⟩
  exact hH.false (g.comp φ)

/-- **Lower bound** `|C_p × C_q, H| ≥ 2p` whenever `C_q ↛ H`. -/
theorem nhf_tensor_cycles_ge_gen (hP : Odd P) (hQ : Odd Q) (hPQ : P ≤ Q) {H : SimpleGraph W}
    (hH : IsEmpty (cycleGraph Q →g H)) :
    ((2 * P : ℕ) : ℕ∞) ≤ nhf (tensor (cycleGraph P) (cycleGraph Q)) H := by
  apply le_nhf
  intro S ⟨g⟩
  have hm := fun (ω : Fin P × Fin Q × Bool) => walk_meets_gen k l hP hQ hPQ hH S g ω.1 ω.2.1 ω.2.2
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

/-- **Theorem.** For odd `3 ≤ p ≤ q` and any `H` with an edge and `C_q ↛ H`,
`|C_p × C_q, H| = 2p`. -/
theorem nhf_tensor_cycles_target (hP : Odd P) (hQ : Odd Q) (hPQ : P ≤ Q) {H : SimpleGraph W}
    (hH : IsEmpty (cycleGraph Q →g H)) {u w : W} (huw : H.Adj u w) :
    nhf (tensor (cycleGraph P) (cycleGraph Q)) H = ((2 * P : ℕ) : ℕ∞) := by
  apply le_antisymm _ (nhf_tensor_cycles_ge_gen k l hP hQ hPQ hH)
  have hK2 : (⊤ : SimpleGraph (Fin 2)) →g H :=
    ⟨![u, w], by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all [huw.symm]⟩
  exact (nhf_le_of_hom_target hK2).trans (nhf_tensor_cycles_le k l hQ)

/-- If `C_q → H` then `|C_p × C_q, H| = 0`. -/
theorem nhf_tensor_cycles_zero {H : SimpleGraph W} (φ : cycleGraph Q →g H) :
    nhf (tensor (cycleGraph P) (cycleGraph Q)) H = 0 :=
  nhf_eq_zero_of_hom (φ.comp (tensorSnd _ _))

/-- **Corollary.** For odd `3 ≤ p ≤ q < m` (`m` odd), `|C_p × C_q, C_m| = 2p`. -/
theorem nhf_tensor_cycles_cycle (j : ℕ) (hP : Odd P) (hQ : Odd Q) (hPQ : P ≤ Q)
    (hQm : Q < j + 3) :
    nhf (tensor (cycleGraph P) (cycleGraph Q)) (cycleGraph (j + 3)) = ((2 * P : ℕ) : ℕ∞) :=
  nhf_tensor_cycles_target k l hP hQ hPQ (no_hom_cycle_of_odd_lt (l + 3) (j + 3) (by omega) hQ hQm)
    ((cyc_adj_iff 0 1).mpr (Or.inl (by ring)))

end NonHom
