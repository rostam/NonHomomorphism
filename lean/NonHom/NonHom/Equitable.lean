import NonHom.Regular

/-!
# Equitable 3-colourings and `γ(·, K₃)` of regular graphs

**Theorem.** Let `G` be `d`-regular (`d ≥ 1`) on `n` vertices and suppose `G` has an *equitable*
proper 3-colouring (class sizes pairwise differ by at most 1). Then
`2·γ(G, K₃) = d·M(n)` with `M(n) = ⌈n/3⌉ + [n ≡ 2 (mod 3)]`.

By the Chen–Lih–Wu theorem every connected cubic graph other than `K₄` and `K₃,₃` has an
equitable 3-colouring, giving `γ(G,K₃) = 3⌈n/6⌉` (that theorem is cited, not formalized).
Here we formalize the general statement and apply it to hypercubes, using the equitable
colouring `x ↦ |x| mod 3`.
-/

open SimpleGraph Finset

namespace NonHom

local notation "K3" => (⊤ : SimpleGraph (Fin 3))

/-- `M(n) = ⌈n/3⌉ + [n ≡ 2 (mod 3)]`, the least maximum of a same-parity triple summing to `n`. -/
def Mtri (n : ℕ) : ℕ := (n + 2) / 3 + if n % 3 = 2 then 1 else 0

theorem max_triple_eq (a b c n : ℕ) (hs : a + b + c = n) (h1 : a ≤ b + 1) (h2 : b ≤ a + 1)
    (h3 : a ≤ c + 1) (h4 : c ≤ a + 1) (h5 : b ≤ c + 1) (h6 : c ≤ b + 1) :
    max (max ((a : ℤ) + b - c) ((a : ℤ) + c - b)) ((b : ℤ) + c - a) = (Mtri n : ℤ) := by
  unfold Mtri
  obtain ⟨t, r, hr, rfl⟩ : ∃ t r, r < 3 ∧ n = 3 * t + r := ⟨n / 3, n % 3, Nat.mod_lt _ (by norm_num),
    (Nat.div_add_mod n 3).symm⟩
  have ha : a = t ∨ a = t + 1 := by omega
  have hb : b = t ∨ b = t + 1 := by omega
  have hc : c = t ∨ c = t + 1 := by omega
  interval_cases r <;>
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    first | omega | (split_ifs <;> push_cast <;> simp only [max_def] <;> split_ifs <;> omega)

theorem Mtri_lower (n : ℕ) : ∀ s₁ s₂ s₃ : ℤ, 0 ≤ s₁ → 0 ≤ s₂ → 0 ≤ s₃ → s₁ + s₂ + s₃ = n →
    s₁ % 2 = s₂ % 2 → s₂ % 2 = s₃ % 2 →
    (Mtri n : ℤ) ≤ s₁ ∨ (Mtri n : ℤ) ≤ s₂ ∨ (Mtri n : ℤ) ≤ s₃ := by
  intro s₁ s₂ s₃ h1 h2 h3 hs p1 p2
  unfold Mtri
  split_ifs <;> push_cast <;> omega

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Equitable-colouring theorem.** -/
theorem gamma_K3_equitable {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) (f : G →g K3)
    (heq : ∀ i j, cls f i ≤ cls f j + 1) :
    2 * gamma G K3 = ((d * Mtri (Fintype.card V) : ℕ) : ℕ∞) := by
  apply le_antisymm
  · exact gamma_K3_upper hreg f _ (max_triple_eq _ _ _ _ (cls_sum f) (heq 0 1) (heq 1 0)
      (heq 0 2) (heq 2 0) (heq 1 2) (heq 2 1))
  · exact gamma_K3_lower hd hreg _ (Mtri_lower _)

/-! ### Hypercubes -/

/-- Weight of a 0/1 vector. -/
def wt {d : ℕ} (x : Fin d → Bool) : ℕ := ∑ i, if x i then 1 else 0

/-- The hypercube `Q_d`: vectors differing in exactly one coordinate. -/
def cube (d : ℕ) : SimpleGraph (Fin d → Bool) where
  Adj x y := (univ.filter fun i => x i ≠ y i).card = 1
  symm := ⟨fun x y h => by simpa [ne_comm] using h⟩
  loopless := ⟨fun x h => by simp at h⟩

instance (d : ℕ) : DecidableRel (cube d).Adj := fun x y =>
  inferInstanceAs (Decidable ((univ.filter fun i => x i ≠ y i).card = 1))

/-- Flip coordinate `i`. -/
def flip {d : ℕ} (x : Fin d → Bool) (i : Fin d) : Fin d → Bool := Function.update x i (!x i)

theorem cube_adj_iff {d : ℕ} (x y : Fin d → Bool) : (cube d).Adj x y ↔ ∃ i, y = flip x i := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := card_eq_one.mp h
    refine ⟨i, funext fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      have : x j ≠ y j := by
        have := (Finset.ext_iff.mp hi j).mpr (mem_singleton_self j)
        simpa using this
      simp only [flip, Function.update_self]
      cases hx : x j <;> cases hy : y j <;> simp_all
    · have : ¬ x j ≠ y j := by
        intro hne
        have := (Finset.ext_iff.mp hi j).mp (by simpa using hne)
        exact hj (mem_singleton.mp this)
      push Not at this
      simp [flip, Function.update_of_ne hj, this]
  · rintro ⟨i, rfl⟩
    show (univ.filter fun j => x j ≠ flip x i j).card = 1
    rw [card_eq_one]
    refine ⟨i, ?_⟩
    ext j
    rw [mem_filter, mem_singleton]
    by_cases hj : j = i
    · subst hj; simp [flip, Function.update_self]
    · simp [flip, Function.update_of_ne hj, hj]

theorem flip_injective {d : ℕ} (x : Fin d → Bool) : Function.Injective (flip x) := by
  intro i j h
  by_contra hij
  have := congrFun h i
  simp [flip, Function.update_of_ne hij] at this

theorem cube_regular (d : ℕ) : (cube d).IsRegularOfDegree d := by
  intro x
  rw [← card_neighborFinset_eq_degree]
  have : (cube d).neighborFinset x = univ.image (flip x) := by
    ext y
    rw [mem_neighborFinset, cube_adj_iff, mem_image]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i, mem_univ _, rfl⟩
    · rintro ⟨i, -, rfl⟩; exact ⟨i, rfl⟩
  rw [this, card_image_of_injective _ (flip_injective x), card_univ, Fintype.card_fin]

theorem wt_flip {d : ℕ} (x : Fin d → Bool) (i : Fin d) :
    wt (flip x i) + (if x i then 1 else 0) = wt x + (if x i then 0 else 1) := by
  unfold wt flip
  have h1 := Finset.sum_update_of_mem (mem_univ i) (fun j => if x j then 1 else 0)
    (if (!x i) then 1 else 0)
  have e : (fun j => if Function.update x i (!x i) j then 1 else 0) =
      Function.update (fun j => if x j then 1 else 0) i (if (!x i) then 1 else 0) := by
    funext j; by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [e, h1]
  rw [← Finset.add_sum_erase _ _ (mem_univ i)]
  rw [show (univ \ {i} : Finset (Fin d)) = univ.erase i by ext; simp]
  cases x i <;> simp <;> ring

/-- The weight colouring `x ↦ |x| mod 3`. -/
def cubeCol (d : ℕ) : cube d →g K3 where
  toFun x := ⟨wt x % 3, Nat.mod_lt _ (by norm_num)⟩
  map_rel' := by
    intro x y h
    obtain ⟨i, rfl⟩ := (cube_adj_iff x y).mp h
    have h' := wt_flip x i
    simp only [top_adj, ne_eq, Fin.mk.injEq]
    by_cases hx : x i = true <;> simp [hx] at h' <;> omega

/-- Number of vectors of weight `≡ c (mod 3)`. -/
def Ncnt (d c : ℕ) : ℕ := (univ.filter fun x : Fin d → Bool => wt x % 3 = c).card

theorem wt_cons {d : ℕ} (b : Bool) (x : Fin d → Bool) :
    wt (Fin.cons b x : Fin (d + 1) → Bool) = (if b then 1 else 0) + wt x := by
  rw [wt, wt, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem Ncnt_succ (d c : ℕ) (hc : c < 3) : Ncnt (d + 1) c = Ncnt d c + Ncnt d ((c + 2) % 3) := by
  unfold Ncnt
  simp only [card_filter]
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (d + 1) => Bool))
    (fun p => if ((if p.1 then 1 else 0) + wt p.2) % 3 = c then 1 else 0)
    (fun x => if wt x % 3 = c then 1 else 0) (fun p => by
      show _ = (if wt (Fin.cons p.1 p.2 : Fin (d + 1) → Bool) % 3 = c then 1 else 0)
      rw [wt_cons])]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [add_comm]
  congr 1
  · apply sum_congr rfl; intro x _; simp
  · apply sum_congr rfl
    intro x _
    have : (1 + wt x) % 3 = c ↔ wt x % 3 = (c + 2) % 3 := by omega
    simp only [if_true, this]

/-- The three weight classes are equitable. -/
theorem Ncnt_equitable (d : ℕ) : ∀ a b, a < 3 → b < 3 → Ncnt d a ≤ Ncnt d b + 1 := by
  induction d with
  | zero =>
    intro a b ha hb
    have h0 : Ncnt 0 0 = 1 := by decide
    have h1 : Ncnt 0 1 = 0 := by decide
    have h2 : Ncnt 0 2 = 0 := by decide
    interval_cases a <;> interval_cases b <;> omega
  | succ d ih =>
    intro a b ha hb
    have r0 := Ncnt_succ d 0 (by norm_num)
    have r1 := Ncnt_succ d 1 (by norm_num)
    have r2 := Ncnt_succ d 2 (by norm_num)
    simp only [Nat.reduceMod, Nat.reduceAdd] at r0 r1 r2
    have i01 := ih 0 1 (by norm_num) (by norm_num); have i10 := ih 1 0 (by norm_num) (by norm_num)
    have i02 := ih 0 2 (by norm_num) (by norm_num); have i20 := ih 2 0 (by norm_num) (by norm_num)
    have i12 := ih 1 2 (by norm_num) (by norm_num); have i21 := ih 2 1 (by norm_num) (by norm_num)
    interval_cases a <;> interval_cases b <;> omega

theorem cls_cubeCol (d : ℕ) (i : Fin 3) : cls (cubeCol d) i = Ncnt d i.val := by
  unfold cls Ncnt
  congr 1
  try (ext x; simp [cubeCol, Fin.ext_iff])

/-- **Hypercubes.** `2·γ(Q_d, K₃) = d·M(2^d)` for `d ≥ 1`, i.e. `γ(Q_d,K₃) = d(2^d+2)/6` for even
`d` and `d(2^d+4)/6` for odd `d`. -/
theorem gamma_cube (d : ℕ) (hd : 0 < d) :
    2 * gamma (cube d) K3 = ((d * Mtri (2 ^ d) : ℕ) : ℕ∞) := by
  have h := gamma_K3_equitable hd (cube_regular d) (cubeCol d) (fun i j => by
    rw [cls_cubeCol, cls_cubeCol]; exact Ncnt_equitable d _ _ i.isLt j.isLt)
  rwa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h

/-- The closed forms. -/
theorem Mtri_two_pow (d : ℕ) : Mtri (2 ^ d) = if d % 2 = 0 then (2 ^ d + 2) / 3 else (2 ^ d + 4) / 3 := by
  have key : ∀ d, 2 ^ d % 3 = if d % 2 = 0 then 1 else 2 := by
    intro d
    induction d with
    | zero => simp
    | succ d ih => rw [pow_succ, Nat.mul_mod, ih]; split_ifs <;> omega
  have := key d
  unfold Mtri
  rcases Nat.mod_two_eq_zero_or_one d with h | h
  · have h3 : 2 ^ d % 3 = 1 := by rw [this, if_pos h]
    rw [if_pos h, if_neg (by omega)]; omega
  · have h3 : 2 ^ d % 3 = 2 := by rw [this, if_neg (by omega)]
    rw [if_pos h3, if_neg (show ¬ d % 2 = 0 by omega)]; omega

end NonHom
