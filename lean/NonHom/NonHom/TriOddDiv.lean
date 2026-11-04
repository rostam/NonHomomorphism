import NonHom.TriangularR
import NonHom.Turan

/-!
# Triangular graphs `L(K_n)` into `K_r`, odd `n`, `r ∣ n - 1`

Let `n = 2m+1` and `n - 1 = q·r`.

* `q` even: `|L(K_n), K_r| = n·r·C(q,2)` (the Turán bound).
* `q` odd: `|L(K_n), K_r| = n·r·C(q,2) + r/2`.

**Construction.** The edges of `K_n` with centre `h` (`2h ≡ u + w` in `ℤ_n`) form a near-perfect
matching missing `h`. Colour each edge by a colour assigned to its centre class; the class `0`
(edges `{u,-u}`) is instead coloured like the class of its smaller endpoint. If every colour
gets `q` nonzero classes, a vertex `v` sees exactly `q` edges of every colour, except when
`v > m` and the classes `v, -v` have different colours, where one colour has `q+1` and another
`q-1` edges (cost `+1`).
-/

open SimpleGraph Finset

namespace NonHom

local notation "Kn" n => (⊤ : SimpleGraph (Fin n))

/-- The centre `h` of a pair `{u,w}` of `ℤ_n` (`2h ≡ u + w`), computed from `x = u + w`. -/
def cen (n x : ℕ) : ℕ :=
  if x % 2 = 0 then (if x / 2 < n then x / 2 else x / 2 - n)
  else if (x + n) / 2 < n then (x + n) / 2 else (x + n) / 2 - n

/-- Class index of the edge `{a,b}`: its centre, or the smaller endpoint when `a + b = n`. -/
def key (n a b : ℕ) : ℕ := if a + b = n then min a b else cen n (a + b)

theorem key_comm (n a b : ℕ) : key n a b = key n b a := by
  unfold key; rw [Nat.add_comm, Nat.min_comm]

/-- Edge colouring of `K_n` from a colouring of the classes. -/
def cirCol {n r : ℕ} (col : ℕ → Fin r) (e : (Kn n).edgeSet) : Fin r :=
  Sym2.lift ⟨fun u w : Fin n => col (key n u.val w.val), fun u w => by show col (key n u w) = col (key n w u); rw [key_comm]⟩ e.1

theorem dcol_cirCol {n r : ℕ} (col : ℕ → Fin r) (v : Fin n) (i : Fin r) :
    dcol (cirCol (n := n) col) v i =
      (univ.filter fun u : Fin n => u ≠ v ∧ col (key n v.val u.val) = i).card := by
  unfold dcol
  symm
  apply card_bij (fun u hu => (⟨⟨s(v, u), by
      simp only [mem_filter, mem_univ, true_and] at hu
      exact (top_adj v u).mpr (Ne.symm hu.1)⟩, Sym2.mem_mk_left v u⟩ : At (Kn n) v))
  · intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu ⊢
    simpa [cirCol] using hu.2
  · intro u hu u' hu' h
    have h' := congrArg (fun z : At (Kn n) v => (z.1 : Sym2 (Fin n))) h
    exact Sym2.congr_right.mp h'
  · rintro ⟨⟨e, he⟩, hv⟩ hcol
    simp only [mem_filter, mem_univ, true_and] at hcol
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp hv
    refine ⟨u, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨fun h => ((SimpleGraph.mem_edgeSet _).mp he).ne h.symm, ?_⟩
    simpa [cirCol] using hcol

/-- Colour counts at `v` compared with the class counts. -/
theorem cir_count {m n r : ℕ} (hn : n = 2 * m + 1) (col : ℕ → Fin r) (v : Fin n) (i : Fin r) :
    (univ.filter fun u : Fin n => u ≠ v ∧ col (key n v.val u.val) = i).card +
      (if v.val ≠ 0 ∧ col v.val = i then 1 else 0) =
    (univ.filter fun h : Fin n => h.val ≠ 0 ∧ col h.val = i).card +
      (if v.val ≠ 0 ∧ col (min v.val (n - v.val)) = i then 1 else 0) := by
  have hv := v.isLt
  set S := univ.filter fun u : Fin n => u ≠ v ∧ col (key n v.val u.val) = i
  have h1 := card_filter_add_card_filter_not (s := S) (fun u => v.val + u.val = n)
  have h2 : (S.filter fun u => v.val + u.val = n).card =
      if v.val ≠ 0 ∧ col (min v.val (n - v.val)) = i then 1 else 0 := by
    split_ifs with h
    · rw [card_eq_one]
      refine ⟨⟨n - v.val, by omega⟩, ?_⟩
      ext u
      simp only [S, mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff, ne_eq, key]
      have := u.isLt
      constructor
      · rintro ⟨-, h'⟩; omega
      · intro hu
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        rw [ite_eq_left (by omega), show u.val = n - v.val by omega]; exact congrArg Fin.val h.2
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro u hu hsum
      have hu' := (mem_filter.mp hu).2
      simp only [key, ite_eq_left hsum] at hu'
      apply h
      have := u.isLt
      refine ⟨by omega, ?_⟩
      rw [show n - v.val = u.val by omega]; exact hu'.2
  have h3 : (S.filter fun u => ¬ v.val + u.val = n).card =
      (univ.filter fun h : Fin n => h.val ≠ 0 ∧ h ≠ v ∧ col h.val = i).card := by
    apply card_bij (fun u _ => (⟨cen n (v.val + u.val), by unfold cen; split_ifs <;> omega⟩ : Fin n))
    · intro u hu
      have hu1 := (mem_filter.mp (mem_filter.mp hu).1).2
      have hu2 := (mem_filter.mp hu).2
      simp only [key, Fin.ext_iff, ne_eq] at hu1 hu2
      rw [ite_eq_right hu2] at hu1
      simp only [mem_filter, mem_univ, true_and, Fin.ext_iff, ne_eq]
      have := u.isLt
      refine ⟨?_, ?_, hu1.2⟩ <;> unfold cen <;> split_ifs <;> omega
    · intro u _ u' _ h
      simp only [Fin.mk.injEq] at h
      have := u.isLt; have := u'.isLt
      apply Fin.ext
      unfold cen at h; split_ifs at h <;> omega
    · intro h hh
      simp only [mem_filter, mem_univ, true_and, Fin.ext_iff, ne_eq] at hh
      have := h.isLt
      obtain ⟨u0, hu0, hc, hne, hs⟩ : ∃ u0, u0 < n ∧ cen n (v.val + u0) = h.val ∧ u0 ≠ v.val ∧
          v.val + u0 ≠ n := by
        by_cases h1 : v.val ≤ 2 * h.val
        · by_cases h2 : 2 * h.val - v.val < n
          · refine ⟨2 * h.val - v.val, ?_⟩; unfold cen; split_ifs <;> omega
          · refine ⟨2 * h.val - v.val - n, ?_⟩; unfold cen; split_ifs <;> omega
        · refine ⟨2 * h.val + n - v.val, ?_⟩; unfold cen; split_ifs <;> omega
      refine ⟨⟨u0, hu0⟩, ?_, Fin.ext hc⟩
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, hs⟩
      simp only [key, Fin.ext_iff, ne_eq]
      rw [ite_eq_right hs, hc]
      exact ⟨hne, hh.2.2⟩
  have h4 := card_filter_add_card_filter_not
    (s := univ.filter fun h : Fin n => h.val ≠ 0 ∧ col h.val = i) (fun h => h = v)
  have h5 : ((univ.filter fun h : Fin n => h.val ≠ 0 ∧ col h.val = i).filter fun h => h = v).card =
      if v.val ≠ 0 ∧ col v.val = i then 1 else 0 := by
    rw [filter_filter]
    split_ifs with h
    · rw [card_eq_one]
      refine ⟨v, ?_⟩
      ext u; simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨-, rfl⟩; rfl
      · rintro rfl; exact ⟨h, rfl⟩
    · rw [card_eq_zero, filter_eq_empty_iff]; rintro u - ⟨hu, rfl⟩; exact h hu
  have h6 : ((univ.filter fun h : Fin n => h.val ≠ 0 ∧ col h.val = i).filter fun h => ¬ h = v) =
      univ.filter fun h : Fin n => h.val ≠ 0 ∧ h ≠ v ∧ col h.val = i := by
    ext u; simp only [mem_filter, mem_univ, true_and]; tauto
  rw [h6] at h4
  omega

/-- Per-vertex cost: all counts `q`, or one `q+1` and one `q-1`. -/
theorem cost_vertex {r q : ℕ} (g : Fin r → ℕ) (a b : Fin r) (δ : Prop) [Decidable δ]
    (hg : ∀ i, g i + (if δ ∧ b = i then 1 else 0) = q + (if δ ∧ a = i then 1 else 0))
    (hs : ∑ i, g i = r * q) :
    ∑ i, (g i).choose 2 ≤ r * q.choose 2 + (if δ ∧ a ≠ b then 1 else 0) := by
  have h2 := two_sum_choose g hs
  have hd : ∀ i, ((g i : ℤ) - q) =
      ((if δ ∧ a = i then 1 else 0 : ℕ) : ℤ) - ((if δ ∧ b = i then 1 else 0 : ℕ) : ℤ) := by
    intro i
    have := hg i
    by_cases h1 : δ ∧ a = i <;> by_cases h2 : δ ∧ b = i <;>
      simp only [h1, h2, ite_false] at this ⊢ <;> omega
  have hb : ∑ i, ((g i : ℤ) - q) ^ 2 ≤ 2 * ((if δ ∧ a ≠ b then 1 else 0 : ℕ) : ℤ) := by
    by_cases hdf : δ ∧ a ≠ b
    · rw [ite_eq_left hdf]
      calc ∑ i, ((g i : ℤ) - q) ^ 2 ≤
            ∑ i, ((if a = i then 1 else 0) + (if b = i then 1 else 0) : ℤ) := by
            apply sum_le_sum; intro i _; rw [hd i]
            by_cases h1 : a = i <;> by_cases h2 : b = i
            · exact absurd (h1.trans h2.symm) hdf.2
            all_goals simp [h1, h2, hdf.1]
        _ = 2 := by rw [sum_add_distrib, sum_ite_eq, sum_ite_eq]; simp
    · rw [ite_eq_right hdf, sum_eq_zero]
      · simp
      intro i _
      rw [hd i]
      by_cases hδ : δ
      · have hab : a = b := by by_contra h; exact hdf ⟨hδ, h⟩
        subst hab; simp
      · simp [hδ]
  generalize (if δ ∧ a ≠ b then 1 else 0 : ℕ) = D at hb ⊢
  have : (2 * ∑ i, (g i).choose 2 : ℤ) ≤ 2 * ((r * q.choose 2 : ℕ) : ℤ) + 2 * (D : ℤ) := by
    push_cast at h2 ⊢; linarith
  have : 2 * ∑ i, (g i).choose 2 ≤ 2 * (r * q.choose 2) + 2 * D := by
    exact_mod_cast this
  omega

/-- **Core upper bound** for the centre-class colouring. -/
theorem cir_upper {m n r q : ℕ} (hn : n = 2 * m + 1) (hqr : n - 1 = q * r) (col : ℕ → Fin r)
    (hfib : ∀ i, (univ.filter fun h : Fin n => h.val ≠ 0 ∧ col h.val = i).card = q) :
    nhf (Kn n).lineGraph (⊤ : SimpleGraph (Fin r)) ≤
      ((n * (r * q.choose 2) +
        (univ.filter fun v : Fin n => v.val ≠ 0 ∧ col (min v.val (n - v.val)) ≠ col v.val).card :
          ℕ) : ℕ∞) := by
  refine (line_upper_r (d := 0) (cirCol (n := n) col)).trans ?_
  rw [sum_congr rfl fun v _ => card_mono_r (top_regular n) (cirCol col) v]
  norm_cast
  have hv : ∀ v : Fin n, ∑ i, (dcol (cirCol (n := n) col) v i).choose 2 ≤
      r * q.choose 2 + (if v.val ≠ 0 ∧ col (min v.val (n - v.val)) ≠ col v.val then 1 else 0) := by
    intro v
    apply cost_vertex _ (col (min v.val (n - v.val))) (col v.val) (v.val ≠ 0)
    · intro i; rw [dcol_cirCol]; have := cir_count hn col v i; rw [hfib i] at this; exact this
    · rw [sum_dcol (top_regular n), hqr, mul_comm]
  calc _ ≤ ∑ v : Fin n, (r * q.choose 2 +
        (if v.val ≠ 0 ∧ col (min v.val (n - v.val)) ≠ col v.val then 1 else 0)) :=
        sum_le_sum fun v _ => hv v
    _ = _ := by
      rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, ← card_filter]

/-! ### Counting classes by circular distance -/

theorem cnt_le {n K : ℕ} (hK : 2 * K < n) :
    (univ.filter fun h : Fin n => h.val ≠ 0 ∧ min (n - h.val) h.val ≤ K).card = 2 * K := by
  rw [card_filter, Fin.sum_univ_eq_sum_range (fun x => if x ≠ 0 ∧ min (n - x) x ≤ K then 1 else 0) n]
  exact count_near n K hK

theorem cnt_between {n A B : ℕ} (hAB : A ≤ B) (hB : 2 * B < n) :
    (univ.filter fun h : Fin n =>
      h.val ≠ 0 ∧ A < min (n - h.val) h.val ∧ min (n - h.val) h.val ≤ B).card = 2 * (B - A) := by
  have h1 := card_filter_add_card_filter_not
    (s := univ.filter fun h : Fin n => h.val ≠ 0 ∧ min (n - h.val) h.val ≤ B)
    (fun h => min (n - h.val) h.val ≤ A)
  rw [filter_filter, filter_filter, cnt_le hB] at h1
  have e1 : (univ.filter fun h : Fin n =>
      (h.val ≠ 0 ∧ min (n - h.val) h.val ≤ B) ∧ min (n - h.val) h.val ≤ A) =
      univ.filter fun h : Fin n => h.val ≠ 0 ∧ min (n - h.val) h.val ≤ A := by
    ext h; simp only [mem_filter, mem_univ, true_and]; omega
  have e2 : (univ.filter fun h : Fin n =>
      (h.val ≠ 0 ∧ min (n - h.val) h.val ≤ B) ∧ ¬ min (n - h.val) h.val ≤ A) =
      univ.filter fun h : Fin n =>
        h.val ≠ 0 ∧ A < min (n - h.val) h.val ∧ min (n - h.val) h.val ≤ B := by
    ext h; simp only [mem_filter, mem_univ, true_and]; omega
  rw [e1, e2, cnt_le (by omega)] at h1
  omega

theorem div_eq_iff_bounds {T s i : ℕ} (hs : 0 < s) : T / s = i ↔ i * s ≤ T ∧ T < i * s + s := by
  rw [← Nat.le_div_iff_mul_le hs, show i * s + s = (i + 1) * s by ring,
    ← Nat.div_lt_iff_lt_mul hs]
  omega

theorem mul_gap {a b q : ℕ} (h : a < b) : a * q + q ≤ b * q := by
  have := Nat.mul_le_mul_right q (show a + 1 ≤ b by omega)
  rwa [add_mul, one_mul] at this

/-! ### `q` even -/

/-- Class `x` gets colour `⌊(t-1)/s⌋` where `t` is the circular distance of `x` from `0`. -/
def colA (n s r : ℕ) (hr : 0 < r) (x : ℕ) : Fin r :=
  ⟨min ((min (n - x) x - 1) / s) (r - 1), by omega⟩

theorem fib_colA {m n s r : ℕ} (hr : 0 < r) (hn : n = 2 * m + 1) (hm : m = s * r) (hs : 0 < s)
    (i : Fin r) :
    (univ.filter fun h : Fin n => h.val ≠ 0 ∧ colA n s r hr h.val = i).card = 2 * s := by
  have hi := i.isLt
  have hle : i.val * s + s ≤ m := by rw [hm, mul_comm s]; exact mul_gap hi
  have e : (univ.filter fun h : Fin n => h.val ≠ 0 ∧ colA n s r hr h.val = i) =
      univ.filter fun h : Fin n => h.val ≠ 0 ∧ i.val * s < min (n - h.val) h.val ∧
        min (n - h.val) h.val ≤ i.val * s + s := by
    ext h
    simp only [mem_filter, mem_univ, true_and, colA, Fin.ext_iff]
    have := h.isLt
    by_cases h0 : h.val = 0
    · simp [h0]
    have hT : min (n - h.val) h.val - 1 < r * s := by rw [mul_comm, ← hm]; omega
    rw [min_eq_left (Nat.le_sub_one_of_lt ((Nat.div_lt_iff_lt_mul hs).mpr hT)),
      div_eq_iff_bounds hs]
    omega
  rw [e, cnt_between (by omega) (by omega)]
  omega

/-- **Triangular graphs, odd `n`, `n - 1 = q·r`, `q` even**: upper bound `n·r·C(q,2)`. -/
theorem tri_upper_odd_div_even (n q r : ℕ) (hn : n % 2 = 1) (h3 : 3 ≤ n) (hqr : n - 1 = q * r)
    (hq : q % 2 = 0) :
    nhf (Kn n).lineGraph (⊤ : SimpleGraph (Fin r)) ≤ ((n * (r * q.choose 2) : ℕ) : ℕ∞) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, q = 2 * s := ⟨q / 2, by omega⟩
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; simp at hqr; omega
    · exact h
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; simp at hqr; omega
    · exact h
  have hm : m = s * r := by
    rw [show 2 * m + 1 - 1 = 2 * m by omega] at hqr; linarith
  have h := cir_upper rfl hqr (colA (2 * m + 1) s r hr) (fun i => fib_colA hr rfl hm hs i)
  have hD : (univ.filter fun v : Fin (2 * m + 1) => v.val ≠ 0 ∧
      colA (2 * m + 1) s r hr (min v.val (2 * m + 1 - v.val)) ≠ colA (2 * m + 1) s r hr v.val) = ∅ := by
    rw [filter_eq_empty_iff]
    rintro v - ⟨-, hne⟩
    apply hne
    have : min (2 * m + 1 - min v.val (2 * m + 1 - v.val)) (min v.val (2 * m + 1 - v.val)) =
        min (2 * m + 1 - v.val) v.val := by have := v.isLt; omega
    simp only [colA, this]
  rwa [hD, card_empty, add_zero] at h

/-! ### `q` odd -/

/-- `q = 2s+1`: the classes at distance `t` with `t - 1 = J q + k` go to colour `2J` (`k < s`),
`2J+1` (`s ≤ k < 2s`), or are split by sign (`k = 2s`). -/
def colB (n q s r : ℕ) (hr : 0 < r) (x : ℕ) : Fin r :=
  ⟨min (2 * ((min (n - x) x - 1) / q) +
    (if (min (n - x) x - 1) % q < s then 0 else if (min (n - x) x - 1) % q < 2 * s then 1
      else if 2 * x < n then 0 else 1)) (r - 1), by omega⟩

theorem fib_colB {m n s p : ℕ} (hn : n = 2 * m + 1) (hm : m = p * (2 * s + 1)) (hp : 0 < 2 * p)
    (i : Fin (2 * p)) :
    (univ.filter fun h : Fin n => h.val ≠ 0 ∧ colB n (2 * s + 1) s (2 * p) hp h.val = i).card =
      2 * s + 1 := by
  have hq : 0 < 2 * s + 1 := by omega
  obtain ⟨J, e0, he0, hi⟩ : ∃ J e0, e0 < 2 ∧ i.val = 2 * J + e0 :=
    ⟨i.val / 2, i.val % 2, by omega, by omega⟩
  have he0s : (e0 = 0 ∧ e0 * s = 0) ∨ (e0 = 1 ∧ e0 * s = s) := by
    interval_cases e0 <;> simp
  have hJ : J < p := by have := i.isLt; omega
  have hJq : J * (2 * s + 1) + (2 * s + 1) ≤ m := by rw [hm]; exact mul_gap hJ
  set q := 2 * s + 1 with hq_def
  set c := if e0 = 0 then J * q + q else n - (J * q + q) with hc
  have hchar : ∀ h : Fin n, (h.val ≠ 0 ∧ colB n q s (2 * p) hp h.val = i) ↔
      (h.val ≠ 0 ∧ J * q + e0 * s < min (n - h.val) h.val ∧
        min (n - h.val) h.val ≤ J * q + e0 * s + s) ∨ h.val = c := by
    intro h
    have := h.isLt
    by_cases h0 : h.val = 0
    · constructor
      · rintro ⟨h1, -⟩; exact absurd h0 h1
      · rintro (⟨h1, -⟩ | h2)
        · exact absurd h0 h1
        · rw [hc] at h2; split_ifs at h2 <;> omega
    have hdm := Nat.div_add_mod' (min (n - h.val) h.val - 1) q
    have hk : (min (n - h.val) h.val - 1) % q < q := Nat.mod_lt _ hq
    have hJ0 : (min (n - h.val) h.val - 1) / q < p := by
      by_contra hcon
      push Not at hcon
      have := Nat.mul_le_mul_right q hcon
      omega
    have hval : (colB n q s (2 * p) hp h.val).val = 2 * ((min (n - h.val) h.val - 1) / q) +
        (if (min (n - h.val) h.val - 1) % q < s then 0
          else if (min (n - h.val) h.val - 1) % q < 2 * s then 1
          else if 2 * h.val < n then 0 else 1) := by
      simp only [colB]
      rw [min_eq_left]
      split_ifs <;> omega
    rw [Fin.ext_iff, hval, hi, hc]
    generalize (min (n - h.val) h.val - 1) / q = J0 at hdm hJ0
    generalize (min (n - h.val) h.val - 1) % q = k at hdm hk
    rcases lt_trichotomy J0 J with hlt | heq | hgt
    · have := mul_gap (q := q) hlt; split_ifs <;> omega
    · subst heq; split_ifs <;> omega
    · have := mul_gap (q := q) hgt; split_ifs <;> omega
  have e : (univ.filter fun h : Fin n => h.val ≠ 0 ∧ colB n q s (2 * p) hp h.val = i) =
      (univ.filter fun h : Fin n => h.val ≠ 0 ∧ J * q + e0 * s < min (n - h.val) h.val ∧
        min (n - h.val) h.val ≤ J * q + e0 * s + s) ∪ univ.filter fun h : Fin n => h.val = c := by
    rw [← filter_or]; ext h; simp only [mem_filter, mem_univ, true_and]; exact hchar h
  have hc1 : (univ.filter fun h : Fin n => h.val = c).card = 1 := by
    rw [card_eq_one]
    refine ⟨⟨c, by rw [hc]; split_ifs <;> omega⟩, ?_⟩
    ext h; simp [Fin.ext_iff]
  rw [e, card_union_of_disjoint, hc1, cnt_between (by omega) (by omega)]
  · omega
  · rw [disjoint_filter]
    rintro h - ⟨-, -, h2⟩ h3
    rw [h3, hc] at h2
    split_ifs at h2 <;> omega

theorem defect_colB {m n s p : ℕ} (hn : n = 2 * m + 1) (hm : m = p * (2 * s + 1))
    (hp : 0 < 2 * p) :
    (univ.filter fun v : Fin n => v.val ≠ 0 ∧
      colB n (2 * s + 1) s (2 * p) hp (min v.val (n - v.val)) ≠
        colB n (2 * s + 1) s (2 * p) hp v.val).card ≤ p := by
  have hq : 0 < 2 * s + 1 := by omega
  set q := 2 * s + 1 with hq_def
  -- a defect lies above `m` and is in a split class
  have hdef : ∀ v : Fin n, v.val ≠ 0 →
      colB n q s (2 * p) hp (min v.val (n - v.val)) ≠ colB n q s (2 * p) hp v.val →
      m < v.val ∧ 2 * s ≤ (min (n - v.val) v.val - 1) % q := by
    intro v h0 hne
    have := v.isLt
    have hty : min (n - min v.val (n - v.val)) (min v.val (n - v.val)) = min (n - v.val) v.val := by
      omega
    by_contra hcon
    apply hne
    apply Fin.ext
    simp only [colB, hty]
    have hk := Nat.mod_lt (min (n - v.val) v.val - 1) hq
    split_ifs <;> omega
  calc _ ≤ (range p).card := by
        apply card_le_card_of_injOn (fun v : Fin n => (min (n - v.val) v.val - 1) / q)
        · intro v hv
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv
          simp only [coe_range, Set.mem_Iio]
          have := v.isLt
          by_contra hcon
          push Not at hcon
          have := Nat.mul_le_mul_right q hcon
          have := Nat.div_mul_le_self (min (n - v.val) v.val - 1) q
          omega
        · intro v hv v' hv' hf
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv hv'
          have d1 := hdef v hv.1 hv.2
          have d2 := hdef v' hv'.1 hv'.2
          have k1 := Nat.mod_lt (min (n - v.val) v.val - 1) hq
          have k2 := Nat.mod_lt (min (n - v'.val) v'.val - 1) hq
          have m1 := Nat.div_add_mod' (min (n - v.val) v.val - 1) q
          have m2 := Nat.div_add_mod' (min (n - v'.val) v'.val - 1) q
          simp only at hf
          rw [hf] at m1
          have := v.isLt; have := v'.isLt
          apply Fin.ext
          omega
    _ = p := card_range p

/-- **Triangular graphs, odd `n`, `n - 1 = q·r`, `q` odd**: upper bound `n·r·C(q,2) + r/2`. -/
theorem tri_upper_odd_div_odd (n q r : ℕ) (hn : n % 2 = 1) (h3 : 3 ≤ n) (hqr : n - 1 = q * r)
    (hq : q % 2 = 1) :
    nhf (Kn n).lineGraph (⊤ : SimpleGraph (Fin r)) ≤
      ((n * (r * q.choose 2) + r / 2 : ℕ) : ℕ∞) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, q = 2 * s + 1 := ⟨q / 2, by omega⟩
  have hr2 : r % 2 = 0 := by
    have h2 : 2 * m = (2 * s + 1) * r := by omega
    have : (2 * s + 1) * r = 2 * (s * r) + r := by ring
    omega
  obtain ⟨p, rfl⟩ : ∃ p, r = 2 * p := ⟨r / 2, by omega⟩
  have hp : 0 < 2 * p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h; simp at hqr; omega
    · omega
  have hm : m = p * (2 * s + 1) := by
    rw [show 2 * m + 1 - 1 = 2 * m by omega] at hqr; linarith
  have h := cir_upper rfl hqr (colB (2 * m + 1) (2 * s + 1) s (2 * p) hp)
    (fun i => fib_colB rfl hm hp i)
  refine h.trans ?_
  have := defect_colB rfl hm hp
  rw [show 2 * p / 2 = p by omega]
  exact_mod_cast Nat.add_le_add_left this _

/-! ### Exact values -/

theorem tri_turan_div (q r : ℕ) (hr : 0 < r) :
    (q * r).choose 2 - turanNumber (q * r) r = r * q.choose 2 := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have := turanNumber_add_formula q 0 r'
  simp only [zero_add, add_zero, zero_mul] at this
  omega

/-- **Triangular graphs, odd `n`, `n - 1 = q·r`, `q` even**: `|L(K_n), K_r| = n·r·C(q,2)`. -/
theorem nhf_triangular_odd_div_even (n q r : ℕ) (hn : n % 2 = 1) (h3 : 3 ≤ n)
    (hqr : n - 1 = q * r) (hq : q % 2 = 0) :
    nhf (Kn n).lineGraph (⊤ : SimpleGraph (Fin r)) = ((n * (r * q.choose 2) : ℕ) : ℕ∞) := by
  apply le_antisymm (tri_upper_odd_div_even n q r hn h3 hqr hq)
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; simp at hqr; omega
    · exact h
  have h := line_lower_clique (top_regular n) (H := (⊤ : SimpleGraph (Fin r)))
    (r := r) (cliqueFree_of_card_lt (by simp))
  rwa [Fintype.card_fin, hqr, tri_turan_div q r hr] at h

/-- **Triangular graphs, odd `n`, `n - 1 = q·r`, `q` odd**: `|L(K_n), K_r| = n·r·C(q,2) + r/2`. -/
theorem nhf_triangular_odd_div_odd (n q r : ℕ) (hn : n % 2 = 1) (h3 : 3 ≤ n)
    (hqr : n - 1 = q * r) (hq : q % 2 = 1) :
    nhf (Kn n).lineGraph (⊤ : SimpleGraph (Fin r)) =
      ((n * (r * q.choose 2) + r / 2 : ℕ) : ℕ∞) :=
  le_antisymm (tri_upper_odd_div_odd n q r hn h3 hqr hq) (tri_lower_parity n q r hn hqr hq)

end NonHom
