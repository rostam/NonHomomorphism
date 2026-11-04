import NonHom.Equitable
import NonHom.TensorTarget

/-!
# Folded cubes

The folded cube `FQ_n` (`n = k + 1`) has vertex set `{0,1}^k`; `x ~ y` iff they differ in exactly
one coordinate or in all coordinates. For odd `n` it has odd girth `n`.

**Theorem.** For odd `n ≥ 3` and every `H` with an edge such that `C_n ↛ H`,
`|FQ_n, H| = 2^{n-2}`.

Lower bound: for each `x` the walk that flips coordinates `0, 1, …, k-1` in turn and then
complements is a closed walk of length `n`, i.e. a map `C_n → FQ_n`; each edge lies on at most two
of these `2^k` walks. Upper bound: delete the `2^{k-1}` antipodal edges and 2-colour by parity.
-/

open SimpleGraph Finset

namespace NonHom

variable (j : ℕ) {W : Type*}

local notation "k" => 2 * j + 2

/-- The folded cube on `{0,1}^k`. -/
def folded : SimpleGraph (Fin k → Bool) where
  Adj x y := (univ.filter fun i => x i ≠ y i).card = 1 ∨ ∀ i, x i ≠ y i
  symm := ⟨fun x y h => by
    rcases h with h | h
    · left; simpa [ne_comm] using h
    · right; intro i; exact (h i).symm⟩
  loopless := ⟨fun x h => by
    rcases h with h | h
    · simp at h
    · exact h ⟨0, by omega⟩ rfl⟩

instance : DecidableRel (folded j).Adj := fun x y =>
  inferInstanceAs (Decidable (_ ∨ _))

/-- The walk: after `t` steps the first `t` coordinates are flipped. -/
def fw (x : Fin k → Bool) (t : ℕ) : Fin k → Bool := fun i => xor (x i) (decide (i.val < t))

theorem fw_injective (t : ℕ) : Function.Injective (fun x : Fin k → Bool => fw j x t) := by
  intro x y h
  funext i
  simpa [fw] using congrFun h i

/-- Coordinates where consecutive walk vertices differ. -/
theorem fw_diff_step (x : Fin k → Bool) (t : ℕ) (ht : t < k) :
    (univ.filter fun i : Fin k => fw j x t i ≠ fw j x (t + 1) i) = {⟨t, ht⟩} := by
  ext i
  rw [mem_filter, mem_singleton, Fin.ext_iff]
  simp only [mem_univ, true_and, fw]
  by_cases h : i.val = t
  · simp [h]
  · have e : (i.val < t ↔ i.val < t + 1) := by omega
    simp [h, e]

theorem fw_diff_last (x : Fin k → Bool) : ∀ i : Fin k, fw j x k i ≠ fw j x 0 i := by
  intro i; simp [fw, i.isLt]

/-- The walk as a homomorphism from `C_n`. -/
def fwHom (x : Fin k → Bool) : cycleGraph (2 * j + 3) →g folded j where
  toFun i := fw j x i.val
  map_rel' := by
    intro u v huv
    have step : ∀ u : Fin (2 * j + 3), (folded j).Adj (fw j x u.val) (fw j x ((u + 1 : Fin (2 * j + 3)).val)) := by
      intro u
      rw [Fin.val_add_one]
      split_ifs with hu
      · right
        rw [hu, Fin.val_last]
        intro i; simp [fw, i.isLt]
      · left
        have hlt : u.val < k := by
          have := u.isLt; have : u.val ≠ 2 * j + 2 := fun h => hu (Fin.ext h); omega
        rw [fw_diff_step j x u.val hlt, card_singleton]
    rcases (cyc_adj_iff u v).mp huv with rfl | rfl
    · exact step u
    · exact (step v).symm

/-- Difference set of an unordered pair. -/
def dset (e : Sym2 (Fin k → Bool)) : Finset (Fin k) :=
  Sym2.lift ⟨fun a b => univ.filter fun i => a i ≠ b i, fun a b => by simp [ne_comm]⟩ e

/-- The step edge at time `t`. -/
def fedge (x : Fin k → Bool) (t : Fin (2 * j + 3)) : Sym2 (Fin k → Bool) :=
  s(fw j x t.val, fw j x ((t + 1 : Fin (2 * j + 3)).val))

theorem dset_mk (a b : Fin k → Bool) : dset j s(a, b) = univ.filter fun i => a i ≠ b i := rfl

theorem fedge_val_succ (t : Fin (2 * j + 3)) (ht : t.val < k) :
    ((t + 1 : Fin (2 * j + 3)) : ℕ) = t.val + 1 := by
  rw [Fin.val_add_one]; split_ifs with h
  · rw [h, Fin.val_last] at ht; omega
  · rfl

theorem fedge_val_last (t : Fin (2 * j + 3)) (ht : t.val = k) :
    ((t + 1 : Fin (2 * j + 3)) : ℕ) = 0 := by
  rw [Fin.val_add_one, if_pos (Fin.ext (by rw [ht, Fin.val_last]))]

theorem dset_fedge_step (x : Fin k → Bool) (t : Fin (2 * j + 3)) (ht : t.val < k) :
    dset j (fedge j x t) = {⟨t.val, ht⟩} := by
  rw [fedge, fedge_val_succ j t ht, dset_mk, fw_diff_step j x t.val ht]

theorem dset_fedge_last (x : Fin k → Bool) (t : Fin (2 * j + 3)) (ht : t.val = k) :
    dset j (fedge j x t) = univ := by
  rw [fedge, fedge_val_last j t ht, dset_mk, ht]
  ext i; simp [fw, i.isLt]

/-- Two walks using the same edge do so at the same time. -/
theorem fedge_time {x x' : Fin k → Bool} {t t' : Fin (2 * j + 3)}
    (h : fedge j x t = fedge j x' t') : t = t' := by
  have hd := congrArg (dset j) h
  have hk : 2 ≤ k := by omega
  have ht := t.isLt; have ht' := t'.isLt
  by_cases h1 : t.val = k <;> by_cases h2 : t'.val = k
  · exact Fin.ext (h1.trans h2.symm)
  · rw [dset_fedge_last j x t h1, dset_fedge_step j x' t' (by omega)] at hd
    have := congrArg Finset.card hd
    rw [card_univ, Fintype.card_fin, card_singleton] at this; omega
  · rw [dset_fedge_step j x t (by omega), dset_fedge_last j x' t' h2] at hd
    have := congrArg Finset.card hd
    rw [card_univ, Fintype.card_fin, card_singleton] at this; omega
  · rw [dset_fedge_step j x t (by omega), dset_fedge_step j x' t' (by omega)] at hd
    have := Finset.singleton_injective hd
    exact Fin.ext (by simpa using congrArg Fin.val this)

/-- **Lower bound.** If `C_n ↛ H` then `|FQ_n, H| ≥ 2^{n-2}`. -/
theorem folded_lower {H : SimpleGraph W} (hH : IsEmpty (cycleGraph (2 * j + 3) →g H)) :
    ((2 ^ (2 * j + 1) : ℕ) : ℕ∞) ≤ nhf (folded j) H := by
  classical
  apply le_nhf
  intro S ⟨g⟩
  have hit : ∀ x : Fin k → Bool, ∃ t, fedge j x t ∈ S := by
    intro x
    by_contra hcon
    push Not at hcon
    apply hH.false
    refine g.comp ⟨fun i => fw j x i.val, fun {u v} huv => ?_⟩
    rw [deleteEdges_adj]
    refine ⟨(fwHom j x).map_rel huv, fun hmem => ?_⟩
    rcases (cyc_adj_iff u v).mp huv with rfl | rfl
    · exact hcon u hmem
    · apply hcon v; rw [fedge, Sym2.eq_swap]; exact hmem
  choose t ht using hit
  let E : (Fin k → Bool) → Sym2 (Fin k → Bool) := fun x => fedge j x (t x)
  have hfib : ∀ e ∈ (univ : Finset (Fin k → Bool)).image E,
      ((univ : Finset (Fin k → Bool)).filter fun x => E x = e).card ≤ 2 := by
    intro e he
    obtain ⟨x₀, -, rfl⟩ := mem_image.mp he
    set t₀ := t x₀
    obtain ⟨a, b, hab⟩ : ∃ a b, fedge j x₀ t₀ = s(a, b) := ⟨_, _, rfl⟩
    calc _ ≤ ({a, b} : Finset (Fin k → Bool)).card := by
          apply card_le_card_of_injOn (fun x => fw j x t₀.val)
          · intro x hx
            simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, E] at hx
            have htt : t x = t₀ := fedge_time j hx
            rw [htt, hab] at hx
            have hm : fw j x t₀.val ∈ s(a, b) := by
              rw [← hx, fedge]; exact Sym2.mem_mk_left _ _
            simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
            exact Sym2.mem_iff.mp hm
          · intro x _ y _ hxy; exact fw_injective j t₀.val hxy
      _ ≤ 2 := card_le_two
  have hcard := card_le_mul_card_image (univ : Finset (Fin k → Bool)) 2 hfib
  have himg : ((univ : Finset (Fin k → Bool)).image E).card ≤ S.card :=
    card_le_card (fun e he => by obtain ⟨x, -, rfl⟩ := mem_image.mp he; exact ht x)
  rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcard
  have : 2 ^ (2 * j + 1) ≤ S.card := by
    have : 2 ^ (2 * j + 2) = 2 * 2 ^ (2 * j + 1) := by ring
    omega
  exact_mod_cast this

theorem card_first_false :
    (univ.filter fun x : Fin k → Bool => x ⟨0, by omega⟩ = false).card = 2 ^ (2 * j + 1) := by
  rw [card_filter]
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (2 * j + 2) => Bool))
    (fun p => if p.1 = false then 1 else 0) (fun x => if x ⟨0, by omega⟩ = false then 1 else 0)
    (fun p => by simp [Fin.consEquiv])]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp

/-- **Upper bound.** `|FQ_n, K₂| ≤ 2^{n-2}`. -/
theorem folded_upper_K2 : nhf (folded j) (⊤ : SimpleGraph (Fin 2)) ≤ ((2 ^ (2 * j + 1) : ℕ) : ℕ∞) := by
  classical
  let z : Fin k := ⟨0, by omega⟩
  let S : Finset (Sym2 (Fin k → Bool)) :=
    (univ.filter fun x : Fin k → Bool => x z = false).image fun x => s(x, fun i => !x i)
  have hS : S.card ≤ 2 ^ (2 * j + 1) := card_image_le.trans (card_first_false j).le
  have hhom : Nonempty ((folded j).deleteEdges ↑S →g (⊤ : SimpleGraph (Fin 2))) := by
    refine ⟨⟨fun x => ⟨wt x % 2, Nat.mod_lt _ (by norm_num)⟩, fun {x y} h => ?_⟩⟩
    rw [deleteEdges_adj] at h
    obtain ⟨hadj, hnot⟩ := h
    rcases hadj with h1 | h2
    · obtain ⟨i, rfl⟩ := (cube_adj_iff x y).mp h1
      have h' := wt_flip x i
      simp only [top_adj, ne_eq, Fin.mk.injEq]
      by_cases hx : x i = true <;> simp [hx] at h' <;> omega
    · exfalso
      apply hnot
      have hy : y = fun i => !x i := by
        funext i; have := h2 i; cases hx : x i <;> cases hy : y i <;> simp_all
      simp only [S, coe_image, coe_filter, Set.mem_image, Set.mem_ofPred_eq, mem_univ, true_and]
      by_cases h0 : x z = false
      · exact ⟨x, h0, by rw [hy]⟩
      · refine ⟨y, by rw [hy]; simpa using h0, ?_⟩
        rw [Sym2.eq_swap, hy]; congr 1; funext i; simp
  exact (nhf_le_card S hhom).trans (by exact_mod_cast hS)

/-- **Folded-cube theorem.** For odd `n = 2j+3` and every `H` with an edge and `C_n ↛ H`,
`|FQ_n, H| = 2^{n-2}`. -/
theorem nhf_folded {H : SimpleGraph W} (hH : IsEmpty (cycleGraph (2 * j + 3) →g H))
    {u w : W} (huw : H.Adj u w) :
    nhf (folded j) H = ((2 ^ (2 * j + 1) : ℕ) : ℕ∞) := by
  apply le_antisymm _ (folded_lower j hH)
  have hK2 : (⊤ : SimpleGraph (Fin 2)) →g H :=
    ⟨![u, w], by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all [huw.symm]⟩
  exact (nhf_le_of_hom_target hK2).trans (folded_upper_K2 j)

/-- `|FQ_n, C_m| = 2^{n-2}` for odd `m > n`. -/
theorem nhf_folded_cycle (i : ℕ) (hm : 2 * j + 3 < i + 3) :
    nhf (folded j) (cycleGraph (i + 3)) = ((2 ^ (2 * j + 1) : ℕ) : ℕ∞) :=
  nhf_folded j (no_hom_cycle_of_odd_lt (2 * j + 3) (i + 3) (by omega) ⟨j + 1, by ring⟩ hm)
    ((cyc_adj_iff 0 1).mpr (Or.inl (zero_add 1).symm))

/-- `|FQ_n, K₂| = 2^{n-2}`. -/
theorem nhf_folded_K2 : nhf (folded j) (⊤ : SimpleGraph (Fin 2)) = ((2 ^ (2 * j + 1) : ℕ) : ℕ∞) := by
  apply nhf_folded j _ (u := 0) (w := 1) (by decide)
  refine ⟨fun φ => ?_⟩
  have h3 := chromaticNumber_cycleGraph_of_odd (2 * j + 3) (by omega) ⟨j + 1, by ring⟩
  have := (Colorable.of_hom φ (by simpa using colorable_of_fintype (⊤ : SimpleGraph (Fin 2)))).chromaticNumber_le
  rw [h3] at this
  exact absurd this (by decide)

end NonHom
