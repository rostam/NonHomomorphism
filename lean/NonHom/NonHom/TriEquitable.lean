import NonHom.TriangularR

/-!
# Triangular graphs `L(K_n)` into `K_r` when `r ∤ n - 1`: an explicit equitable colouring

**Theorem** (`nhf_triangular_equitable`). If `r ≥ 1`, `n ≥ 1` and `r ∤ n - 1`, then for every `H`
with clique number `r`, `|L(K_n), H| = n·(C(n-1,2) - t(n-1,r))`. No parity assumption on `n`.

The lower bound is `line_lower_clique`. The upper bound replaces the Hilton–de Werra theorem by
an explicit equitable `r`-edge-colouring of `K_n`. Write `n - 1 = k r + s` with `0 < s < r`,
`B = [0, k r)`, `A = [k r, n)` and `θ(x) = ⌊x/2⌋ + (x mod 2)·⌈r/2⌉` (a permutation of `[0,r)`
with `2θ(x) ≡ x` or `x - 1 (mod r)`). Colour `{u,w}` by
* `u, w ∈ B`: `θ(u mod r) + θ(w mod r) (mod r)`;
* `u ∈ B`, `w ∈ A`: `(w - k r) + u + r - 1 (mod r)`;
* `u, w ∈ A`: `(u - k r) + (w - k r) (mod s + 1)`.
Every colour then occurs `k` or `k + 1` times at every vertex (`tcol_count`).
-/

open SimpleGraph Finset

namespace NonHom

/-! ### Arithmetic -/

theorem two_choose_add_self (x : ℕ) : 2 * x.choose 2 + x = x * x := by
  rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self x).two_dvd]
  rcases x with _ | x
  · simp
  · rw [Nat.add_sub_cancel]; ring

/-- `t(q r + s, r) + r C(q,2) + q s = C(q r + s, 2)` for `s < r`. -/
theorem turan_add_eq (r s : ℕ) (hs : s < r) :
    ∀ q : ℕ, turanNumber (q * r + s) r + r * q.choose 2 + q * s = (q * r + s).choose 2 := by
  intro q
  induction q with
  | zero =>
    simp only [zero_mul, zero_add, Nat.choose_zero_succ, mul_zero, add_zero]
    have := card_edgeFinset_top_eq_card_choose_two (V := Fin s)
    rw [Fintype.card_fin] at this; convert this; exact turanGraph_eq_top.mpr (Or.inr hs.le)
  | succ q ih =>
    have e : (q + 1) * r + s = (q * r + s) + r := by ring
    rw [Nat.choose_succ_succ' q 1, Nat.choose_one_right, e, turanNumber_add, choose_two_add (q * r + s) r]
    have hr : 1 ≤ r := by omega
    have : (q * r + s) * (r - 1) + (q * r + s) = (q * r + s) * r := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hr]
    linarith

/-- If every `d_i ∈ {q, q+1}` then `∑ C(d_i,2) + r q² = r C(q,2) + q ∑ d_i`. -/
theorem sum_choose_near {r q : ℕ} (d : Fin r → ℕ) (h : ∀ i, q ≤ d i ∧ d i ≤ q + 1) :
    ∑ i, (d i).choose 2 + r * (q * q) = r * q.choose 2 + q * ∑ i, d i := by
  have hi : ∀ i, (d i).choose 2 + q * q = q.choose 2 + q * d i := by
    intro i
    rcases (show d i = q ∨ d i = q + 1 by have := h i; omega) with e | e
    · rw [e]
    · rw [e, Nat.choose_succ_succ' q 1, Nat.choose_one_right]; ring
  have := sum_congr rfl (fun i (_ : i ∈ (univ : Finset (Fin r))) => hi i)
  rw [sum_add_distrib, sum_add_distrib, sum_const, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul, smul_eq_mul, ← mul_sum] at this
  exact this

/-! ### Counting lemmas on `range` -/

theorem sum_periodic (r : ℕ) (f : ℕ → ℕ) :
    ∀ k, ∑ x ∈ range (k * r), f (x % r) = k * ∑ y ∈ range r, f y
  | 0 => by simp
  | k + 1 => by
    rw [show (k + 1) * r = k * r + r by ring, sum_range_add, sum_periodic r f k]
    have : ∀ y ∈ range r, f ((k * r + y) % r) = f y := fun y hy => by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (mem_range.mp hy)]
    rw [sum_congr rfl this]; ring

theorem sum_inj_one {r : ℕ} (g : ℕ → ℕ) (hlt : ∀ y < r, g y < r)
    (hinj : ∀ a < r, ∀ b < r, g a = g b → a = b) {i : ℕ} (hi : i < r) :
    ∑ y ∈ range r, (if g y = i then 1 else 0) = 1 := by
  rw [← card_filter]
  have himg : (range r).image g = range r := by
    apply eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hz
      exact mem_range.mpr (hlt y (mem_range.mp hy))
    · rw [card_image_of_injOn (fun a ha b hb h => hinj a (mem_range.mp ha) b (mem_range.mp hb) h)]
  have hmem : i ∈ (range r).image g := by rw [himg]; exact mem_range.mpr hi
  obtain ⟨y, hy, hgy⟩ := mem_image.mp hmem
  rw [card_eq_one]
  refine ⟨y, ?_⟩
  ext z
  simp only [mem_filter, mem_range, mem_singleton]
  constructor
  · rintro ⟨hz, hgz⟩
    exact hinj z hz y (mem_range.mp hy) (hgz.trans hgy.symm)
  · rintro rfl; exact ⟨mem_range.mp hy, hgy⟩

theorem sum_le_one_of_inj (M : ℕ) (p : ℕ → Prop) [DecidablePred p]
    (h : ∀ a < M, ∀ b < M, p a → p b → a = b) :
    ∑ y ∈ range M, (if p y then 1 else 0) ≤ 1 := by
  rw [← card_filter]
  exact card_le_one.mpr fun a ha b hb =>
    h a (mem_range.mp (mem_filter.mp ha).1) b (mem_range.mp (mem_filter.mp hb).1)
      (mem_filter.mp ha).2 (mem_filter.mp hb).2

theorem one_le_sum_of (M : ℕ) (p : ℕ → Prop) [DecidablePred p] {y : ℕ} (hy : y < M) (hp : p y) :
    1 ≤ ∑ y ∈ range M, (if p y then 1 else 0) := by
  have := single_le_sum (f := fun y => if p y then 1 else 0) (fun _ _ => Nat.zero_le _)
    (mem_range.mpr hy)
  simpa [hp] using this

theorem sum_ne_add (M b : ℕ) (hb : b < M) (P : ℕ → Prop) [DecidablePred P] :
    ∑ x ∈ range M, (if x ≠ b ∧ P x then 1 else 0) + (if P b then 1 else 0) =
      ∑ x ∈ range M, (if P x then 1 else 0) := by
  rw [← sum_erase_add _ _ (mem_range.mpr hb), ← sum_erase_add (range M) (fun x => if P x then 1 else 0)
    (mem_range.mpr hb)]
  simp only [ne_eq, not_true_eq_false, false_and, ite_false, add_zero]
  congr 1
  apply sum_congr rfl
  intro x hx
  rw [if_congr (and_iff_right (ne_of_mem_erase hx)) rfl rfl]

theorem mod_cancel_lt {m a b c : ℕ} (ha : a < m) (hb : b < m) (h : (c + a) % m = (c + b) % m) :
    a = b := by
  have := Nat.ModEq.add_left_cancel' c h
  rwa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-! ### The twist `θ` -/

/-- `θ(x) = ⌊x/2⌋ + (x mod 2)·⌈r/2⌉`, a permutation of `[0,r)` with `2θ(x) ≡ x` or `x - 1`. -/
def theta (r x : ℕ) : ℕ := x / 2 + (x % 2) * ((r + 1) / 2)

theorem theta_lt {r x : ℕ} (hx : x < r) : theta r x < r := by
  unfold theta
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> omega

theorem theta_inj {r a b : ℕ} (ha : a < r) (hb : b < r) (h : theta r a = theta r b) : a = b := by
  unfold theta at h
  rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;>
  rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;> rw [h1, h2] at h <;> omega

theorem theta_two (r x : ℕ) (hr : 0 < r) : ∃ y ≤ 1,
    theta r x + theta r x = y + x + (r - 1) ∨ theta r x + theta r x + r = y + x + (r - 1) := by
  unfold theta
  rcases Nat.mod_two_eq_zero_or_one x with h1 | h1 <;> rw [h1]
  · exact ⟨1, le_rfl, Or.inr (by omega)⟩
  · rcases Nat.mod_two_eq_zero_or_one r with h2 | h2
    · exact ⟨0, by omega, Or.inl (by omega)⟩
    · exact ⟨1, le_rfl, Or.inl (by omega)⟩

/-! ### The colouring

Vertices `[0, n)` with `n = k r + s + 1`, `0 < s < r`: `B = [0, k r)`, `A = [k r, n)`. -/

/-- Colour of the pair `{u, w}`. -/
def tcol (k r s u w : ℕ) : ℕ :=
  if u < k * r ∧ w < k * r then (theta r (u % r) + theta r (w % r)) % r
  else if u < k * r then (w - k * r + u + (r - 1)) % r
  else if w < k * r then (u - k * r + w + (r - 1)) % r
  else (u - k * r + (w - k * r)) % (s + 1)

theorem tcol_symm (k r s u w : ℕ) : tcol k r s u w = tcol k r s w u := by
  unfold tcol
  split_ifs <;> first | omega | rw [add_comm]

theorem tcol_lt {k r s : ℕ} (hsr : s < r) (u w : ℕ) : tcol k r s u w < r := by
  unfold tcol
  split_ifs
  · exact Nat.mod_lt _ (by omega)
  · exact Nat.mod_lt _ (by omega)
  · exact Nat.mod_lt _ (by omega)
  · exact lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hsr

/-- **Key count.** At every vertex every colour occurs `k` or `k + 1` times. -/
theorem tcol_count (k r s v i : ℕ) (hs0 : 0 < s) (hsr : s < r) (hi : i < r) :
    k ≤ ∑ x ∈ range (k * r + s + 1), (if x ≠ v ∧ tcol k r s v x = i then 1 else 0) ∧
    ∑ x ∈ range (k * r + s + 1), (if x ≠ v ∧ tcol k r s v x = i then 1 else 0) ≤ k + 1 := by
  have hr : 0 < r := by omega
  rw [show k * r + s + 1 = k * r + (s + 1) by ring, sum_range_add]
  by_cases hvB : v < k * r
  · -- `v ∈ B`
    set c := theta r (v % r)
    have e1 : ∑ x ∈ range (k * r), (if x ≠ v ∧ tcol k r s v x = i then 1 else 0) =
        ∑ x ∈ range (k * r), (if x ≠ v ∧ (c + theta r (x % r)) % r = i then 1 else 0) :=
      sum_congr rfl (fun x hx => by
        have ht : tcol k r s v x = (c + theta r (x % r)) % r := by
          rw [tcol, ite_eq_left ⟨hvB, mem_range.mp hx⟩]
        rw [ht])
    have h1 := sum_ne_add (k * r) v hvB (fun x => (c + theta r (x % r)) % r = i)
    have h2 : ∑ x ∈ range (k * r), (if (c + theta r (x % r)) % r = i then 1 else 0) = k := by
      have := sum_periodic r (fun y => if (c + theta r y) % r = i then 1 else 0) k
      rw [this, sum_inj_one (fun y => (c + theta r y) % r) (fun y _ => Nat.mod_lt _ hr)
        (fun a ha b hb h => theta_inj ha hb (mod_cancel_lt (theta_lt ha) (theta_lt hb) h)) hi,
        mul_one]
    have e2 : ∑ y ∈ range (s + 1), (if k * r + y ≠ v ∧ tcol k r s v (k * r + y) = i then 1 else 0) =
        ∑ y ∈ range (s + 1), (if (v + (r - 1) + y) % r = i then 1 else 0) := by
      apply sum_congr rfl
      intro y _
      have ht : tcol k r s v (k * r + y) = (v + (r - 1) + y) % r := by
        rw [tcol, ite_eq_right (fun h => by omega), ite_eq_left hvB,
          show k * r + y - k * r + v + (r - 1) = v + (r - 1) + y by omega]
      rw [ht, if_congr (and_iff_right (show k * r + y ≠ v by omega)) rfl rfl]
    have h3 : ∑ y ∈ range (s + 1), (if (v + (r - 1) + y) % r = i then 1 else 0) ≤ 1 :=
      sum_le_one_of_inj _ _ (fun a ha b hb pa pb => mod_cancel_lt (by omega) (by omega) (pa.trans pb.symm))
    have h4 : (if (c + theta r (v % r)) % r = i then 1 else 0) ≤
        ∑ y ∈ range (s + 1), (if (v + (r - 1) + y) % r = i then 1 else 0) := by
      split_ifs with hp
      · obtain ⟨y, hy1, hy⟩ := theta_two r (v % r) hr
        apply one_le_sum_of (s + 1) _ (show y < s + 1 by omega)
        rw [← hp, add_assoc, ← Nat.mod_add_mod]
        rcases hy with hy | hy
        · rw [show c + theta r (v % r) = v % r + (r - 1 + y) by omega]
        · rw [← Nat.add_mod_right (c + theta r (v % r)) r,
            show c + theta r (v % r) + r = v % r + (r - 1 + y) by omega]
      · exact Nat.zero_le _
    rw [e1, e2]
    omega
  · -- `v ∈ A`
    have e1 : ∑ x ∈ range (k * r), (if x ≠ v ∧ tcol k r s v x = i then 1 else 0) =
        ∑ x ∈ range (k * r), (if (v - k * r + (r - 1) + x % r) % r = i then 1 else 0) := by
      apply sum_congr rfl
      intro x hx
      have hx' := mem_range.mp hx
      have ht : tcol k r s v x = (v - k * r + (r - 1) + x % r) % r := by
        rw [tcol, ite_eq_right (fun h => hvB h.1), ite_eq_right hvB, ite_eq_left hx', Nat.add_mod_mod,
          show v - k * r + x + (r - 1) = v - k * r + (r - 1) + x by omega]
      rw [ht, if_congr (and_iff_right (show x ≠ v by omega)) rfl rfl]
    have h2 : ∑ x ∈ range (k * r), (if (v - k * r + (r - 1) + x % r) % r = i then 1 else 0) = k := by
      have := sum_periodic r (fun y => if (v - k * r + (r - 1) + y) % r = i then 1 else 0) k
      rw [this, sum_inj_one (fun y => (v - k * r + (r - 1) + y) % r) (fun y _ => Nat.mod_lt _ hr)
        (fun a ha b hb h => mod_cancel_lt ha hb h) hi, mul_one]
    have e2 : ∑ y ∈ range (s + 1), (if k * r + y ≠ v ∧ tcol k r s v (k * r + y) = i then 1 else 0) =
        ∑ y ∈ range (s + 1), (if k * r + y ≠ v ∧ (v - k * r + y) % (s + 1) = i then 1 else 0) := by
      apply sum_congr rfl
      intro y _
      have ht : tcol k r s v (k * r + y) = (v - k * r + y) % (s + 1) := by
        rw [tcol, ite_eq_right (fun h => hvB h.1), ite_eq_right hvB, ite_eq_right (by omega),
          show k * r + y - k * r = y by omega]
      rw [ht]
    have h3 : ∑ y ∈ range (s + 1), (if k * r + y ≠ v ∧ (v - k * r + y) % (s + 1) = i then 1 else 0) ≤ 1 :=
      sum_le_one_of_inj _ _ (fun a ha b hb pa pb => mod_cancel_lt ha hb (pa.2.trans pb.2.symm))
    rw [e1, h2, e2]
    omega

/-! ### The edge colouring of `K_n` and the upper bound -/

local notation "Kn" n => (⊤ : SimpleGraph (Fin n))

/-- The explicit equitable `r`-edge-colouring of `K_{k r + s + 1}`. -/
def tcolE (k r s : ℕ) (hsr : s < r) : (Kn (k * r + s + 1)).edgeSet → Fin r := fun e =>
  Sym2.lift ⟨fun u w => (⟨tcol k r s u.val w.val, tcol_lt hsr _ _⟩ : Fin r),
    fun u w => Fin.ext (tcol_symm k r s u.val w.val)⟩ e.1

theorem dcol_tcolE (k r s : ℕ) (hsr : s < r) (v : Fin (k * r + s + 1)) (i : Fin r) :
    dcol (tcolE k r s hsr) v i =
      ∑ x ∈ range (k * r + s + 1), (if x ≠ v.val ∧ tcol k r s v.val x = i.val then 1 else 0) := by
  unfold dcol
  have : (univ.filter fun e : At (Kn (k * r + s + 1)) v => tcolE k r s hsr e.1 = i).card =
      (univ.filter fun w : Fin (k * r + s + 1) => w ≠ v ∧ tcol k r s v.val w.val = i.val).card := by
    symm
    apply card_bij (fun u hu => (⟨⟨s(v, u), by
        simp only [mem_filter, mem_univ, true_and] at hu
        exact (top_adj v u).mpr (Ne.symm hu.1)⟩, Sym2.mem_mk_left v u⟩ : At (Kn (k * r + s + 1)) v))
    · intro u hu
      simp only [mem_filter, mem_univ, true_and] at hu ⊢
      simp [tcolE, hu.2]
    · intro u hu u' hu' h
      have h' := congrArg (fun z : At (Kn (k * r + s + 1)) v => (z.1 : Sym2 (Fin (k * r + s + 1)))) h
      exact Sym2.congr_right.mp h'
    · rintro ⟨⟨e, he⟩, hv⟩ hcol
      simp only [mem_filter, mem_univ, true_and] at hcol
      obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp hv
      refine ⟨u, ?_, rfl⟩
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨fun h => ((SimpleGraph.mem_edgeSet _).mp he).ne h.symm, ?_⟩
      simpa [tcolE, Fin.ext_iff] using hcol
  rw [this, card_filter, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro w _
  simp only [ne_eq, Fin.ext_iff]

/-- **Upper bound.** For `r ∤ n - 1` the explicit colouring `tcolE` gives
`|L(K_n), K_r| ≤ n·(C(n-1,2) - t(n-1,r))`. -/
theorem tri_upper_equitable (n r : ℕ) (hn : 1 ≤ n) (hr : 0 < r) (hdiv : (n - 1) % r ≠ 0) :
    nhf (Kn n).lineGraph (⊤ : SimpleGraph (Fin r)) ≤
      ((n * ((n - 1).choose 2 - turanNumber (n - 1) r) : ℕ) : ℕ∞) := by
  classical
  obtain ⟨k, s, hs0, hsr, rfl⟩ : ∃ k s, 0 < s ∧ s < r ∧ n = k * r + s + 1 := by
    refine ⟨(n - 1) / r, (n - 1) % r, by omega, Nat.mod_lt _ hr, ?_⟩
    have := Nat.div_add_mod (n - 1) r
    rw [mul_comm] at this
    omega
  rw [show k * r + s + 1 - 1 = k * r + s by omega]
  refine (line_upper_r (d := k * r + s) (tcolE k r s hsr)).trans ?_
  norm_cast
  have hreg := top_regular (k * r + s + 1)
  have hv : ∀ v : Fin (k * r + s + 1),
      ((⊤ : SimpleGraph (At (Kn (k * r + s + 1)) v)) \
        (⊤ : SimpleGraph (Fin r)).comap (fun e => tcolE k r s hsr e.1)).edgeFinset.card =
        (k * r + s).choose 2 - turanNumber (k * r + s) r := by
    intro v
    rw [card_mono_r hreg]
    have hb : ∀ i, k ≤ dcol (tcolE k r s hsr) v i ∧ dcol (tcolE k r s hsr) v i ≤ k + 1 := by
      intro i
      rw [dcol_tcolE]
      exact tcol_count k r s v.val i.val hs0 hsr i.isLt
    have h1 := sum_choose_near _ hb
    rw [sum_dcol hreg, show k * r + s + 1 - 1 = k * r + s by omega] at h1
    have h2 := turan_add_eq r s hsr k
    have h3 : k * (k * r + s) = r * (k * k) + k * s := by ring
    omega
  rw [sum_congr rfl (fun v _ => hv v), sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- **Triangular graphs, `r ∤ n - 1`.** For every `H` with clique number `r ≥ 1`,
`|L(K_n), H| = n·(C(n-1,2) - t(n-1,r))` (no parity assumption on `n`). -/
theorem nhf_triangular_equitable (n r : ℕ) (hn : 1 ≤ n) (hr : 0 < r) (hdiv : (n - 1) % r ≠ 0)
    {W : Type*} {H : SimpleGraph W} [DecidableEq W] (hcf : H.CliqueFree (r + 1))
    (hK : (⊤ : SimpleGraph (Fin r)) →g H) :
    nhf (Kn n).lineGraph H = ((n * ((n - 1).choose 2 - turanNumber (n - 1) r) : ℕ) : ℕ∞) := by
  apply le_antisymm
  · exact (nhf_le_of_hom_target hK).trans (tri_upper_equitable n r hn hr hdiv)
  · have h := line_lower_clique (top_regular n) hcf
    rwa [Fintype.card_fin] at h

/-- The case `H = K_r`. -/
theorem nhf_triangular_Kr (n r : ℕ) (hn : 1 ≤ n) (hr : 0 < r) (hdiv : (n - 1) % r ≠ 0) :
    nhf (Kn n).lineGraph (⊤ : SimpleGraph (Fin r)) =
      ((n * ((n - 1).choose 2 - turanNumber (n - 1) r) : ℕ) : ℕ∞) :=
  nhf_triangular_equitable n r hn hr hdiv
    (cliqueFree_of_card_lt (by rw [Fintype.card_fin]; omega)) (SimpleGraph.Hom.id)

end NonHom
