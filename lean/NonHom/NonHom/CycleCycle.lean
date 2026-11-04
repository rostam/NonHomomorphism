import NonHom.Theorem3

/-!
# `γ(C_n, C_m)` for odd `m`

**Theorem.** Let `m ≥ 3` be odd, `n ≥ 3`, and `C_n → C_m` (i.e. `n` even or `n ≥ m`). Then
`γ(C_n, C_m)` is the least `M` with `M ≡ n (mod 2)` and `n ≤ m·M`.

For `m = 3` this is Theorem `thm:cycle_gamma`. Lower bound: every edge of `C_m` is used a number
of times congruent to `n` mod 2 (remove the edge; `C_m` minus an edge is a path of even length).
Upper bound: wind once around `C_m` if `n` is odd, then walk out and back.
-/

open SimpleGraph Finset
open Fin.NatCast Fin.CommRing

namespace NonHom

theorem cyc_adj_iff {k : ℕ} (u v : Fin (k + 3)) :
    (cycleGraph (k + 3)).Adj u v ↔ v = u + 1 ∨ u = v + 1 := by
  show (cycleGraph (k + 1 + 2)).Adj u v ↔ _
  rw [cycleGraph_adj]
  constructor
  · rintro (h | h)
    · right; linear_combination h
    · left; linear_combination h
  · rintro (h | h)
    · right; linear_combination h
    · left; linear_combination h

theorem cyc_edge_inj {k : ℕ} {x y : Fin (k + 3)} (h : s(x, x + 1) = s(y, y + 1)) : x = y := by
  rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso; apply two_ne_zero_fin k; linear_combination h2 - h1

theorem cyc_edge_form {k : ℕ} {e : Sym2 (Fin (k + 3))} (he : e ∈ (cycleGraph (k + 3)).edgeSet) :
    ∃ x, e = s(x, x + 1) := by
  induction e using Sym2.ind with
  | _ u v =>
    rcases (cyc_adj_iff u v).mp he with h | h
    · exact ⟨u, by rw [h]⟩
    · exact ⟨v, by rw [h, Sym2.eq_swap]⟩

theorem cyc_edges_eq (k : ℕ) :
    (cycleGraph (k + 3)).edgeFinset = univ.image (fun i : Fin (k + 3) => s(i, i + 1)) := by
  ext e
  rw [mem_edgeFinset, mem_image]
  constructor
  · intro he
    obtain ⟨x, rfl⟩ := cyc_edge_form he
    exact ⟨x, mem_univ _, rfl⟩
  · rintro ⟨i, -, rfl⟩
    exact (cyc_adj_iff i (i + 1)).mpr (Or.inl rfl)

/-- Loads of a homomorphism out of a cycle count the steps of the closed walk. -/
theorem load_cyc {W : Type*} [DecidableEq W] {H : SimpleGraph W} (k : ℕ)
    (f : cycleGraph (k + 3) →g H) (e : Sym2 W) :
    load f e = (univ.filter fun i : Fin (k + 3) => s(f i, f (i + 1)) = e).card := by
  unfold load
  rw [cyc_edges_eq, filter_image, card_image_of_injective _ (fun x y h => cyc_edge_inj h)]
  rfl

section lower

variable (k l : ℕ)

/-- Position along the path `C_m - {x, x+1}` starting from `x + 1`. -/
def pos (x y : Fin (l + 3)) : ℕ := (y - (x + 1)).val

theorem pos_succ (x y : Fin (l + 3)) :
    (y = x → pos l x (y + 1) = 0 ∧ pos l x y = l + 2) ∧
    (y ≠ x → pos l x (y + 1) = pos l x y + 1) := by
  unfold pos
  have hval : ∀ a : Fin (l + 3), (a + 1).val = if a.val = l + 2 then 0 else a.val + 1 := by
    intro a
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < l + 3 by omega)]
    have := a.isLt
    split_ifs with h
    · rw [h, show l + 2 + 1 = l + 3 by omega, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega)]
  have hy : y + 1 - (x + 1) = (y - (x + 1)) + 1 := by ring
  have hneg : ((-1 : Fin (l + 3)) : ℕ) = l + 2 := Fin.coe_neg_one
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h]
    have : x - (x + 1) = -1 := by ring
    rw [show x + 1 - (x + 1) = (x - (x + 1)) + 1 by ring, this, hval, hneg]
    simp
  · rw [hy, hval, if_neg]
    intro h'
    apply h
    have : y - (x + 1) = -1 := by
      apply Fin.ext; rw [h', hneg]
    linear_combination this

/-- Every edge of `C_m` (odd `m`) is used a number of times congruent to `n` mod 2. -/
theorem load_parity (hm : Odd (l + 3)) (f : cycleGraph (k + 3) →g cycleGraph (l + 3))
    (x : Fin (l + 3)) : load f s(x, x + 1) % 2 = (k + 3) % 2 := by
  classical
  obtain ⟨t, ht⟩ := hm
  let P : Fin (k + 3) → ℕ := fun i => pos l x (f i)
  let δ : Fin (k + 3) → ℕ := fun i => if s(f i, f (i + 1)) = s(x, x + 1) then 0 else 1
  have step : ∀ i, P (i + 1) % 2 = (P i + δ i) % 2 := by
    intro i
    have hadj := (cyc_adj_iff (f i) (f (i + 1))).mp (f.map_rel ((cyc_adj_iff i (i + 1)).mpr (Or.inl rfl)))
    simp only [P, δ]
    rcases hadj with h | h
    · rw [h]
      by_cases hx : f i = x
      · obtain ⟨h1, h2⟩ := (pos_succ l x (f i)).1 hx
        rw [h1, h2, if_pos (by rw [hx])]; omega
      · rw [(pos_succ l x (f i)).2 hx, if_neg (fun he => hx (cyc_edge_inj he))]
    · have hs : s(f i, f (i + 1)) = s(f (i + 1), f (i + 1) + 1) := by rw [h, Sym2.eq_swap]
      rw [hs, h]
      by_cases hx : f (i + 1) = x
      · obtain ⟨h1, h2⟩ := (pos_succ l x (f (i + 1))).1 hx
        rw [h1, h2, if_pos (by rw [hx])]; omega
      · rw [(pos_succ l x (f (i + 1))).2 hx, if_neg (fun he => hx (cyc_edge_inj he))]; omega
  have hshift : ∑ i, P (i + 1) = ∑ i, P i :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  have hmod : (∑ i, P i) % 2 = (∑ i, (P i + δ i)) % 2 := by
    rw [← hshift, sum_nat_mod, sum_nat_mod univ 2 (fun i => P i + δ i)]
    congr 1; apply sum_congr rfl; intro i _; exact step i
  rw [sum_add_distrib] at hmod
  have hδ : ∑ i, δ i = (univ.filter fun i : Fin (k + 3) => ¬ s(f i, f (i + 1)) = s(x, x + 1)).card := by
    rw [card_filter]; apply sum_congr rfl; intro i _; simp only [δ]; split_ifs <;> simp_all
  have htot := card_filter_add_card_filter_not (s := (univ : Finset (Fin (k + 3))))
    (fun i => s(f i, f (i + 1)) = s(x, x + 1))
  rw [card_univ, Fintype.card_fin] at htot
  rw [load_cyc]
  omega

/-- The parity condition and pigeonhole: `μ(f) ≡ n (mod 2)` and `n ≤ m·μ(f)`. -/
theorem mu_cyc_props (hm : Odd (l + 3)) (f : cycleGraph (k + 3) →g cycleGraph (l + 3)) :
    mu f % 2 = (k + 3) % 2 ∧ k + 3 ≤ (l + 3) * mu f := by
  constructor
  · obtain ⟨e, he, hmu⟩ := exists_mem_eq_sup (cycleGraph (k + 3)).edgeFinset
      ⟨s(0, 1), by rw [mem_edgeFinset]; exact (cyc_adj_iff 0 1).mpr (Or.inl (by ring))⟩
      (fun e' => load f (e'.map f))
    rw [mu, hmu]
    obtain ⟨x, hx⟩ := cyc_edge_form (f.map_mem_edgeSet (mem_edgeFinset.mp he))
    rw [hx]; exact load_parity k l hm f x
  · have h := card_edgeFinset_le_mul_mu f
    rwa [card_edges_cycle, card_edges_cycle] at h

end lower

section upper

variable (k l : ℕ)

theorem cast_eq_iff_lt {a b : ℕ} (ha : a < l + 3) (hb : b < l + 3) :
    ((a : Fin (l + 3)) = (b : Fin (l + 3))) ↔ a = b := by
  constructor
  · intro h
    have := congrArg Fin.val h
    rwa [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · rintro rfl; rfl

theorem count_cast_le (x : Fin (l + 3)) (s K : ℕ) (hs : s ≤ K * (l + 3)) :
    ∑ j ∈ range s, (if (j : Fin (l + 3)) = x then 1 else 0) ≤ K := by
  rw [← card_filter]
  calc _ ≤ (range K).card := by
        apply card_le_card_of_injOn (fun j => j / (l + 3))
        · intro j hj
          simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hj
          simp only [coe_range, Set.mem_Iio]
          rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
        · intro j hj j' hj' hdiv
          simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hj hj'
          have hmod : j % (l + 3) = j' % (l + 3) := by
            have := congrArg Fin.val (hj.2.trans hj'.2.symm)
            rwa [Fin.val_natCast, Fin.val_natCast] at this
          simp only at hdiv
          rw [← Nat.div_add_mod j (l + 3), ← Nat.div_add_mod j' (l + 3), hdiv, hmod]
    _ = K := card_range K

theorem count_cast_one (x : Fin (l + 3)) :
    ∑ j ∈ range (l + 3), (if (j : Fin (l + 3)) = x then 1 else 0) ≤ 1 := by
  rw [← card_filter]
  apply card_le_one.mpr
  intro a ha b hb
  simp only [mem_filter, mem_range] at ha hb
  exact (cast_eq_iff_lt l ha.1 hb.1).mp (ha.2.trans hb.2.symm)

/-- **Upper bound.** For odd `m`, if `C_n → C_m`, `M ≡ n (mod 2)` and `n ≤ m·M`, some
`f : C_n → C_m` has `μ(f) ≤ M`. -/
theorem mu_cyc_upper (hm : Odd (l + 3)) (hhom : Even (k + 3) ∨ l + 3 ≤ k + 3) (M : ℕ)
    (hM : M % 2 = (k + 3) % 2) (hnM : k + 3 ≤ (l + 3) * M) :
    ∃ f : cycleGraph (k + 3) →g cycleGraph (l + 3), mu f ≤ M := by
  obtain ⟨t, ht⟩ := hm
  set base := if (k + 3) % 2 = 1 then l + 3 else 0 with hbase_def
  have hbase : base ≤ k + 3 ∧ (k + 3 - base) % 2 = 0 := by
    rcases hhom with ⟨u, hu⟩ | h <;> simp only [hbase_def] <;> split_ifs <;> omega
  set s := (k + 3 - base) / 2 with hs_def
  have hn2 : k + 3 = base + 2 * s := by omega
  let g : ℕ → ℕ := fun j => if j ≤ base + s then j else 2 * (base + s) - j
  have gstep : ∀ j < k + 3, g (j + 1) = g j + 1 ∨ g j = g (j + 1) + 1 := by
    intro j hj; simp only [g]; split_ifs <;> omega
  have gzero : g 0 = 0 := by simp [g]
  have gend : ((g (k + 3) : ℕ) : Fin (l + 3)) = 0 := by
    have : g (k + 3) = base := by simp only [g]; split_ifs <;> omega
    rw [this, hbase_def]
    split_ifs
    · exact Fin.natCast_self (l + 3)
    · rfl
  let fv : Fin (k + 3) → Fin (l + 3) := fun i => ((g i.val : ℕ) : Fin (l + 3))
  have fsucc : ∀ i : Fin (k + 3), fv (i + 1) = ((g (i.val + 1) : ℕ) : Fin (l + 3)) := by
    intro i
    simp only [fv]
    rw [Fin.val_add_one]
    split_ifs with h
    · rw [h, Fin.val_last, gzero, show k + 2 + 1 = k + 3 by omega, gend]; rfl
    · rfl
  have fstep : ∀ i : Fin (k + 3), fv (i + 1) = fv i + 1 ∨ fv i = fv (i + 1) + 1 := by
    intro i
    rw [fsucc]
    rcases gstep i.val i.isLt with h | h
    · left; simp only [fv]; rw [h]; push_cast; rfl
    · right; simp only [fv]; rw [h]; push_cast; rfl
  let f : cycleGraph (k + 3) →g cycleGraph (l + 3) := ⟨fv, by
    intro u v huv
    rw [cyc_adj_iff] at huv ⊢
    rcases huv with rfl | rfl
    · exact fstep u
    · exact (fstep v).symm⟩
  refine ⟨f, ?_⟩
  -- the step edge at `i` is `s(a i, a i + 1)` with `a = min (g i) (g (i+1))`
  let a : ℕ → ℕ := fun j => min (g j) (g (j + 1))
  have hstep_edge : ∀ i : Fin (k + 3), s(f i, f (i + 1)) = s(((a i.val : ℕ) : Fin (l + 3)),
      ((a i.val : ℕ) : Fin (l + 3)) + 1) := by
    intro i
    show s(fv i, fv (i + 1)) = _
    rw [fsucc]
    simp only [fv, a]
    rcases gstep i.val i.isLt with h | h
    · rw [h, min_eq_left (by omega)]; push_cast; rfl
    · rw [h, min_eq_right (by omega), Sym2.eq_swap]; push_cast; rfl
  -- load bound
  obtain ⟨K, hK⟩ : ∃ K, M = (k + 3) % 2 + 2 * K := ⟨M / 2, by omega⟩
  have hsK : s ≤ K * (l + 3) := by
    rw [hK] at hnM
    rcases Nat.mod_two_eq_zero_or_one (k + 3) with h | h <;> rw [h] at hnM <;>
      simp only [hbase_def, h] at hn2 <;> simp at hn2 <;> nlinarith
  have hload : ∀ x : Fin (l + 3), load f s(x, x + 1) ≤ M := by
    intro x
    rw [load_cyc]
    have hfilt : (univ.filter fun i : Fin (k + 3) => s(f i, f (i + 1)) = s(x, x + 1)) =
        univ.filter fun i : Fin (k + 3) => ((a i.val : ℕ) : Fin (l + 3)) = x := by
      ext i
      simp only [mem_filter, mem_univ, true_and, hstep_edge]
      exact ⟨cyc_edge_inj, fun h => by rw [h]⟩
    rw [hfilt, card_filter,
      Fin.sum_univ_eq_sum_range (fun j => if ((a j : ℕ) : Fin (l + 3)) = x then 1 else 0) (k + 3)]
    rw [show k + 3 = base + s + s by omega, sum_range_add, sum_range_add]
    have castbase : ∀ y : ℕ, ((base + y : ℕ) : Fin (l + 3)) = (y : Fin (l + 3)) := by
      intro y; push_cast
      have : ((base : ℕ) : Fin (l + 3)) = 0 := by
        rw [hbase_def]; split_ifs
        · exact Fin.natCast_self (l + 3)
        · rfl
      rw [this, zero_add]
    have p1 : ∑ j ∈ range base, (if ((a j : ℕ) : Fin (l + 3)) = x then 1 else 0) ≤ (k + 3) % 2 := by
      have : ∀ j ∈ range base, a j = j := by
        intro j hj; rw [mem_range] at hj; simp only [a, g]; split_ifs <;> omega
      rw [sum_congr rfl (fun j hj => by rw [this j hj])]
      rw [hbase_def]
      split_ifs with h
      · rw [h]; exact count_cast_one l x
      · simp
    have p2 : ∑ j ∈ range s, (if ((a (base + j) : ℕ) : Fin (l + 3)) = x then 1 else 0) ≤ K := by
      have : ∀ j ∈ range s, a (base + j) = base + j := by
        intro j hj; rw [mem_range] at hj; simp only [a, g]; split_ifs <;> omega
      rw [sum_congr rfl (fun j hj => by rw [this j hj, castbase])]
      exact count_cast_le l x s K hsK
    have p3 : ∑ j ∈ range s, (if ((a (base + s + j) : ℕ) : Fin (l + 3)) = x then 1 else 0) ≤ K := by
      have : ∀ j ∈ range s, a (base + s + j) = base + (s - 1 - j) := by
        intro j hj; rw [mem_range] at hj; simp only [a, g]; split_ifs <;> omega
      rw [sum_congr rfl (fun j hj => by rw [this j hj, castbase])]
      rw [sum_range_reflect (fun j => if ((j : ℕ) : Fin (l + 3)) = x then 1 else 0) s]
      exact count_cast_le l x s K hsK
    omega
  apply Finset.sup_le
  intro e he
  obtain ⟨x, hx⟩ := cyc_edge_form (f.map_mem_edgeSet (mem_edgeFinset.mp he))
  rw [hx]; exact hload x

end upper

/-- The least `M` with `M ≡ n (mod 2)` and `n ≤ m·M`. -/
noncomputable def cycM (n m : ℕ) (hm : 0 < m) : ℕ :=
  Nat.find (⟨n, rfl, Nat.le_mul_of_pos_left n hm⟩ : ∃ M, M % 2 = n % 2 ∧ n ≤ m * M)

/-- **Theorem.** For odd `m ≥ 3`, `n ≥ 3` with `C_n → C_m` (`n` even or `n ≥ m`),
`γ(C_n,C_m)` is the least `M` with `M ≡ n (mod 2)` and `n ≤ m·M`. -/
theorem gamma_cycle_cycle (k l : ℕ) (hm : Odd (l + 3)) (hhom : Even (k + 3) ∨ l + 3 ≤ k + 3) :
    gamma (cycleGraph (k + 3)) (cycleGraph (l + 3)) = cycM (k + 3) (l + 3) (by omega) := by
  have hspec := Nat.find_spec (⟨k + 3, rfl, Nat.le_mul_of_pos_left (k + 3) (by omega)⟩ :
    ∃ M, M % 2 = (k + 3) % 2 ∧ k + 3 ≤ (l + 3) * M)
  apply le_antisymm
  · obtain ⟨f, hf⟩ := mu_cyc_upper k l hm hhom _ hspec.1 hspec.2
    exact (gamma_le_mu f).trans (by exact_mod_cast hf)
  · apply le_gamma
    intro f
    have := mu_cyc_props k l hm f
    exact_mod_cast Nat.find_min' _ this

end NonHom
