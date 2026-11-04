import NonHom.CycleCycle

/-!
# Regular graphs into odd cycles

**Theorem.** Let `G` be `d`-regular (`d ≥ 1`) on `n` vertices and `m ≥ 3` odd. Then
`2·γ(G, C_m) ≥ d·M_m(n)`, where `M_m(n)` is the least `M ≡ n (mod 2)` with `mM ≥ n`.
Equality holds as soon as some `f : G → C_m` has all its "alternating class sums"
`s_c = ∑_t (-1)^t |f⁻¹(c-t)|` at most `M_m(n)`.

For `m = 3` this is the `K₃` theorem, for `d = 2` it is the `γ(C_n,C_m)` formula.
The key identity is `2·L_c = d·s_c` for the load `L_c` of the edge `{c, c+1}`.
-/

open SimpleGraph Finset
open Fin.NatCast Fin.CommRing

namespace NonHom

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable (l : ℕ)

local notation "Cm" => cycleGraph (l + 3)

/-- Load of the edge `{c, c+1}`. -/
def Lc (f : G →g Cm) (c : Fin (l + 3)) : ℕ := load f s(c, c + 1)

/-- Degree sum of colour class `c` splits into the loads of the two edges at `c`. -/
theorem degsum_cycle (f : G →g Cm) (c : Fin (l + 3)) :
    ∑ v ∈ univ.filter (fun v => f v = c), G.degree v = Lc l f (c - 1) + Lc l f c := by
  rw [← card_darts_fst_color, card_darts_fst_color_eq_sum]
  have hne : c + 1 ≠ c - 1 := by
    intro h; apply two_ne_zero_fin l; linear_combination h
  rw [Fintype.sum_eq_add (c + 1) (c - 1) hne]
  · rw [← load_eq_card_darts f (show c ≠ c + 1 from fun h => by
        apply two_ne_zero_fin l; linear_combination (-2 : Fin (l + 3)) * h + h - h),
      ← load_eq_card_darts f (show c ≠ c - 1 from fun h => by
        apply two_ne_zero_fin l; linear_combination (2 : Fin (l + 3)) * h - h + h)]
    rw [Lc, Lc, show c - 1 + 1 = c by ring, Sym2.eq_swap (a := c - 1) (b := c)]; ring
  · rintro y ⟨hy1, hy2⟩
    rw [card_eq_zero, filter_eq_empty_iff]
    rintro d - ⟨h1, h2⟩
    have hadj := f.map_rel d.adj
    rw [h1, h2, cyc_adj_iff] at hadj
    rcases hadj with h | h
    · exact hy1 h
    · exact hy2 (by rw [h]; ring)

/-- Telescoping around an odd cycle: if `D c = L (c-1) + L c` then `2 L c = ∑_t (-1)^t D (c - t)`. -/
theorem tele (hm : Odd (l + 3)) (L D : Fin (l + 3) → ℤ) (h : ∀ c, D c = L (c - 1) + L c)
    (c : Fin (l + 3)) : 2 * L c = ∑ t ∈ range (l + 3), (-1) ^ t * D (c - t) := by
  have claim : ∀ k, ∑ t ∈ range k, (-1) ^ t * D (c - t) = L c + (-1) ^ (k + 1) * L (c - k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, ih, h (c - k)]
      have e : c - (k : Fin (l + 3)) - 1 = c - ((k + 1 : ℕ) : Fin (l + 3)) := by push_cast; ring
      rw [e, pow_succ, pow_succ, pow_succ]
      ring
  rw [claim (l + 3), show ((l + 3 : ℕ) : Fin (l + 3)) = 0 from Fin.natCast_self (l + 3), sub_zero]
  obtain ⟨t, ht⟩ := hm
  rw [ht, show 2 * t + 1 + 1 = 2 * (t + 1) by ring, pow_mul]
  simp; ring

/-- Class sizes. -/
def ncls (f : G →g Cm) (c : Fin (l + 3)) : ℕ := (univ.filter fun v => f v = c).card

/-- Alternating class sums `s_c = ∑_t (-1)^t n_{c-t}`. -/
def salt (f : G →g Cm) (c : Fin (l + 3)) : ℤ :=
  ∑ t ∈ range (l + 3), (-1) ^ t * (ncls l f (c - t) : ℤ)

/-- **Key identity** `2·L_c = d·s_c` for `d`-regular `G`. -/
theorem two_Lc {d : ℕ} (hreg : G.IsRegularOfDegree d) (hm : Odd (l + 3)) (f : G →g Cm)
    (c : Fin (l + 3)) : 2 * (Lc l f c : ℤ) = d * salt l f c := by
  have h := tele l hm (fun c => (Lc l f c : ℤ)) (fun c => (d : ℤ) * ncls l f c) (fun c => by
    have := degsum_cycle l f c
    rw [sum_degree_of_regular hreg] at this
    simp only [ncls]; exact_mod_cast this) c
  rw [h, salt, mul_sum]
  apply sum_congr rfl; intro t _; ring

theorem sum_Lc (f : G →g Cm) : ∑ c, Lc l f c = G.edgeFinset.card := by
  rw [card_edgeFinset_eq_sum_load f, cyc_edges_eq, sum_image (fun x _ y _ h => cyc_edge_inj h)]
  rfl

theorem mu_ge_Lc (f : G →g Cm) (c : Fin (l + 3)) : Lc l f c ≤ mu f := load_le_mu f _

theorem mu_le_max_Lc (f : G →g Cm) (M : ℕ) (h : ∀ c, Lc l f c ≤ M) : mu f ≤ M := by
  apply Finset.sup_le
  intro e he
  obtain ⟨x, hx⟩ := cyc_edge_form (f.map_mem_edgeSet (mem_edgeFinset.mp he))
  rw [hx]; exact h x

/-- Properties of the alternating sums for `d`-regular `G`. -/
theorem salt_props {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) (hm : Odd (l + 3))
    (f : G →g Cm) :
    (∀ c, 0 ≤ salt l f c) ∧ (∑ c, salt l f c = Fintype.card V) ∧
      (∀ c, salt l f c % 2 = salt l f 0 % 2) := by
  have hdz : (0 : ℤ) < d := by exact_mod_cast hd
  have key := two_Lc l hreg hm f
  refine ⟨fun c => ?_, ?_, ?_⟩
  · have := key c
    have : (0 : ℤ) ≤ d * salt l f c := by rw [← this]; positivity
    exact (mul_nonneg_iff_of_pos_left hdz).mp this
  · have hE : 2 * G.edgeFinset.card = d * Fintype.card V := by
      rw [← sum_degrees_eq_twice_card_edges, sum_degree_of_regular hreg, card_univ]
    have h1 : (d : ℤ) * ∑ c, salt l f c = d * Fintype.card V := by
      rw [mul_sum, ← sum_congr rfl (fun c _ => key c), ← mul_sum]
      have := sum_Lc l f
      have h2 : (∑ c, (Lc l f c : ℤ)) = G.edgeFinset.card := by exact_mod_cast this
      rw [h2]; exact_mod_cast hE
    exact mul_left_cancel₀ hdz.ne' h1
  · have adj : ∀ c, salt l f c + salt l f (c - 1) = 2 * ncls l f c := by
      intro c
      have hD := degsum_cycle l f c
      rw [sum_degree_of_regular hreg] at hD
      have hz : (d : ℤ) * (salt l f c + salt l f (c - 1)) = d * (2 * ncls l f c) := by
        rw [mul_add, ← key c, ← key (c - 1)]
        have : ((d * ncls l f c : ℕ) : ℤ) = Lc l f (c - 1) + Lc l f c := by
          simp only [ncls]; exact_mod_cast hD
        push_cast at this; linear_combination -2 * this
      exact mul_left_cancel₀ hdz.ne' hz
    have step : ∀ j : ℕ, salt l f (j : Fin (l + 3)) % 2 = salt l f 0 % 2 := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have := adj ((j + 1 : ℕ) : Fin (l + 3))
        rw [show ((j + 1 : ℕ) : Fin (l + 3)) - 1 = (j : Fin (l + 3)) by push_cast; ring] at this
        omega
    intro c
    have := step c.val
    rwa [Fin.cast_val_eq_self] at this

/-- **Lower bound** `d·M_m(n) ≤ 2·γ(G, C_m)`. -/
theorem gamma_oddcycle_lower {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) (hm : Odd (l + 3)) :
    ((d * cycM (Fintype.card V) (l + 3) (by omega) : ℕ) : ℕ∞) ≤ 2 * gamma G Cm := by
  by_cases hhom : Nonempty (G →g Cm)
  · obtain ⟨f, hf⟩ := exists_gamma_eq hhom
    rw [← hf]
    obtain ⟨hnn, hsum, hpar⟩ := salt_props l hd hreg hm f
    obtain ⟨c₀, -, hc₀⟩ := exists_max_image (univ : Finset (Fin (l + 3))) (salt l f) univ_nonempty
    set M := (salt l f c₀).toNat with hM
    have hMz : (M : ℤ) = salt l f c₀ := Int.toNat_of_nonneg (hnn c₀)
    -- `n ≤ m·M`
    have h1 : (Fintype.card V : ℤ) ≤ (l + 3) * M := by
      rw [← hsum, hMz]
      calc ∑ c, salt l f c ≤ ∑ _c : Fin (l + 3), salt l f c₀ := sum_le_sum fun c _ => hc₀ c (mem_univ c)
        _ = (l + 3) * salt l f c₀ := by simp
    -- `M ≡ n (mod 2)`
    have h2 : (Fintype.card V : ℤ) % 2 = (M : ℤ) % 2 := by
      rw [← hsum, Finset.sum_int_mod, sum_congr rfl (fun c _ => hpar c), sum_const, card_univ,
        Fintype.card_fin, nsmul_eq_mul, hMz, hpar c₀]
      obtain ⟨t, ht⟩ := hm
      rcases Int.emod_two_eq_zero_or_one (salt l f 0) with h | h <;> rw [h] <;> push_cast [ht] <;> omega
    have hcyc : cycM (Fintype.card V) (l + 3) (by omega) ≤ M := by
      apply Nat.find_min'
      constructor
      · omega
      · exact_mod_cast h1
    have h3 : d * M ≤ 2 * mu f := by
      have := two_Lc l hreg hm f c₀
      have hL := mu_ge_Lc l f c₀
      have : ((d * M : ℕ) : ℤ) = 2 * Lc l f c₀ := by push_cast; rw [hMz, this]
      have : d * M = 2 * Lc l f c₀ := by exact_mod_cast this
      omega
    have := Nat.mul_le_mul_left d hcyc
    exact_mod_cast this.trans h3
  · rw [not_nonempty_iff] at hhom
    rw [gamma_eq_top_iff.mpr hhom, ENat.mul_top (by norm_num)]
    exact le_top

/-- **Equality criterion.** If some `f` has all alternating sums `≤ M`, then `2·γ(G,C_m) ≤ d·M`. -/
theorem gamma_oddcycle_upper {d : ℕ} (hreg : G.IsRegularOfDegree d) (hm : Odd (l + 3))
    (f : G →g Cm) (M : ℕ) (hs : ∀ c, salt l f c ≤ M) :
    2 * gamma G Cm ≤ ((d * M : ℕ) : ℕ∞) := by
  have hL : ∀ c, Lc l f c ≤ d * M / 2 := by
    intro c
    have := two_Lc l hreg hm f c
    have : 2 * (Lc l f c : ℤ) ≤ d * M := by
      rw [this]; exact mul_le_mul_of_nonneg_left (hs c) (by positivity)
    have : 2 * Lc l f c ≤ d * M := by exact_mod_cast this
    omega
  have hmu := mu_le_max_Lc l f _ hL
  calc 2 * gamma G Cm ≤ 2 * (mu f : ℕ∞) := by gcongr; exact gamma_le_mu f
    _ ≤ ((d * M : ℕ) : ℕ∞) := by
        have : 2 * mu f ≤ d * M := by omega
        exact_mod_cast this

end NonHom
