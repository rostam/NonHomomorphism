import NonHom.Cycles

/-!
# Irregular families (Section `sec:irregular`)

* Observation `obs:book`: `γ(B_k,K₃) = k` and `|B_k,K₂| = 1`.
* Observation `obs:friendship_exact`: `γ(F_k,K₃) = k` and `|F_k,K₂| = k`.
* Observation `obs:wheel_gamma`: `γ(W_n,K₃) = n - 1` for odd `n ≥ 5`.
* Observation `obs:multipartite_gamma`: `γ(K_{p,q,r},K₃) = max(pq, pr, qr)`.

All four use the irregular identity `2·L_{ab} = D_a + D_b - D_c` (`two_load_eq`).
-/

open SimpleGraph Finset

namespace NonHom

local notation "K3" => (⊤ : SimpleGraph (Fin 3))

section general

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem degree_eq_sum_ite (v : V) : G.degree v = ∑ w, if G.Adj v w then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter]

theorem degCls_eq_sum (f : G →g K3) (x : Fin 3) :
    degCls f x = ∑ v, if f v = x then G.degree v else 0 := by
  rw [degCls, sum_filter]

theorem sum_degCls (f : G →g K3) :
    degCls f 0 + degCls f 1 + degCls f 2 = ∑ v, G.degree v := by
  have := Finset.sum_fiberwise (univ : Finset V) f (fun v => G.degree v)
  rw [Fin.sum_univ_three] at this
  exact this

/-- Lower bound on `μ` from one load. -/
theorem mu_ge_of_two_load (f : G →g K3) (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (L : ℕ) (h : (degCls f a : ℤ) + degCls f b - degCls f c = 2 * L) : L ≤ mu f := by
  have := two_load_eq f a b c hab hac hbc
  have : load f s(a, b) = L := by omega
  rw [← this]; exact load_le_mu f _

/-- Exact value of `μ` from the three degree sums. -/
theorem mu_eq_of_degCls (f : G →g K3) (M : ℕ)
    (h : max (max ((degCls f 0 : ℤ) + degCls f 1 - degCls f 2)
      ((degCls f 0 : ℤ) + degCls f 2 - degCls f 1)) ((degCls f 1 : ℤ) + degCls f 2 - degCls f 0) =
      2 * M) : mu f = M := by
  have := two_mu_eq_deg f
  omega

theorem third_pair : ∀ c : Fin 3, ∃ a b : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c := by decide

theorem perm_sum (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (D : Fin 3 → ℕ) :
    D 0 + D 1 + D 2 = D a + D b + D c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all <;> ring

theorem third_color' (x y : Fin 3) (h : x ≠ y) :
    ∃ c : Fin 3, c ≠ x ∧ c ≠ y ∧ ∀ z : Fin 3, z ≠ x → z ≠ y → z = c := by
  revert x y; decide

end general

/-! ### Book graphs -/

section book

variable (k : ℕ)

/-- Book graph `B_k`: spine `inl 0 — inl 1`, pages `inr i` adjacent to both spine vertices. -/
def bookAdj : Fin 2 ⊕ Fin k → Fin 2 ⊕ Fin k → Prop
  | .inl a, .inl b => a ≠ b
  | .inl _, .inr _ => True
  | .inr _, .inl _ => True
  | .inr _, .inr _ => False

instance : DecidableRel (bookAdj k) := fun u v => by
  cases u <;> cases v <;> unfold bookAdj <;> infer_instance

def book : SimpleGraph (Fin 2 ⊕ Fin k) where
  Adj := bookAdj k
  symm := ⟨by
    rintro (a | a) (b | b) h <;> simp only [bookAdj] at h ⊢ <;>
      first | exact Ne.symm h | trivial | exact h.elim⟩
  loopless := ⟨by rintro (a | a) h <;> simp [bookAdj] at h⟩

instance : DecidableRel (book k).Adj := inferInstanceAs (DecidableRel (bookAdj k))

theorem book_deg_inl (a : Fin 2) : (book k).degree (.inl a) = k + 1 := by
  rw [degree_eq_sum_ite, Fintype.sum_sum_type]
  fin_cases a <;> simp [book, bookAdj, Fin.sum_univ_two] <;> omega

theorem book_deg_inr (p : Fin k) : (book k).degree (.inr p) = 2 := by
  rw [degree_eq_sum_ite, Fintype.sum_sum_type]
  simp [book, bookAdj]

theorem book_degCls (f : book k →g K3) (x : Fin 3) :
    degCls f x = (if f (.inl 0) = x then k + 1 else 0) + (if f (.inl 1) = x then k + 1 else 0) +
      ∑ p : Fin k, if f (.inr p) = x then 2 else 0 := by
  rw [degCls_eq_sum, Fintype.sum_sum_type, Fin.sum_univ_two]
  simp only [book_deg_inl, book_deg_inr]

/-- **Observation `obs:book`**: `γ(B_k,K₃) = k` for `k ≥ 1`. -/
theorem gamma_book (hk : 1 ≤ k) : gamma (book k) K3 = k := by
  apply le_antisymm
  · -- the colouring spine ↦ 0,1 and pages ↦ 2
    let f : book k →g K3 := ⟨Sum.elim (fun j => Fin.castSucc j) (fun _ => 2), by
      rintro (a | a) (b | b) h <;> simp_all [book, bookAdj, Fin.ext_iff] <;> omega⟩
    have hd : ∀ x : Fin 3, degCls f x = (if (0 : Fin 3) = x then k + 1 else 0) +
        (if (1 : Fin 3) = x then k + 1 else 0) + (if (2 : Fin 3) = x then 2 * k else 0) := by
      intro x
      rw [book_degCls]
      congr 1
      show (∑ p : Fin k, if (2 : Fin 3) = x then 2 else 0) = _
      split_ifs with h <;> simp [h, mul_comm]
    have := mu_eq_of_degCls f k (by
      rw [hd 0, hd 1, hd 2]; simp only [max_def]; norm_num; split_ifs <;> omega)
    calc gamma (book k) K3 ≤ mu f := gamma_le_mu f
      _ = k := by rw [this]
  · apply le_gamma
    intro f
    have hab : f (.inl 0) ≠ f (.inl 1) := f.map_rel (by simp [book, bookAdj])
    obtain ⟨c, hca, hcb, hc⟩ := third_color' _ _ hab
    have hp : ∀ p, f (.inr p) = c := fun p =>
      hc _ (f.map_rel (show (book k).Adj (.inr p) (.inl 0) by simp [book, bookAdj]))
        (f.map_rel (show (book k).Adj (.inr p) (.inl 1) by simp [book, bookAdj]))
    have h := mu_ge_of_two_load f (f (.inl 0)) c (f (.inl 1)) (Ne.symm hca) hab hcb k (by
      rw [book_degCls, book_degCls, book_degCls]
      simp only [hp, if_pos rfl, if_neg hab, if_neg (Ne.symm hab), if_neg hca, if_neg hcb,
        if_neg (Ne.symm hca), if_neg (Ne.symm hcb), sum_const, card_univ, Fintype.card_fin,
        smul_eq_mul]
      push_cast; ring)
    exact_mod_cast h

/-- **Observation `obs:book`**: `|B_k,K₂| = 1` for `k ≥ 1`. -/
theorem nhf_book_K2 (hk : 1 ≤ k) : nhf (book k) (⊤ : SimpleGraph (Fin 2)) = 1 := by
  apply le_antisymm
  · have h := nhf_le_card (G := book k) (H := (⊤ : SimpleGraph (Fin 2))) {s(.inl 0, .inl 1)}
      ⟨⟨Sum.elim (fun _ => 0) (fun _ => 1), by
        rintro (a | a) (b | b) h <;> simp only [deleteEdges_adj] at h <;>
          simp_all [book, bookAdj] <;> fin_cases a <;> fin_cases b <;> simp_all [Sym2.eq_swap]⟩⟩
    simpa using h
  · -- `B_k` contains a triangle, so it is not bipartite
    rw [ENat.one_le_iff_ne_zero]
    intro h0
    obtain ⟨g⟩ := nhf_eq_zero_iff.mp h0
    have h1 := g.map_rel (show (book k).Adj (.inl 0) (.inl 1) by simp [book, bookAdj])
    have h2 := g.map_rel (show (book k).Adj (.inl 0) (.inr ⟨0, hk⟩) by simp [book, bookAdj])
    have h3 := g.map_rel (show (book k).Adj (.inl 1) (.inr ⟨0, hk⟩) by simp [book, bookAdj])
    simp only [top_adj] at h1 h2 h3
    revert h1 h2 h3
    generalize g (.inl 0) = x; generalize g (.inl 1) = y; generalize g (.inr ⟨0, hk⟩) = z
    revert x y z; decide

end book

/-! ### Friendship graphs -/

section friendship

variable (k : ℕ)

/-- Friendship graph `F_k`: hub `none`, triangle `i` on `none, some (i,0), some (i,1)`. -/
def frAdj : Option (Fin k × Fin 2) → Option (Fin k × Fin 2) → Prop
  | none, none => False
  | none, some _ => True
  | some _, none => True
  | some (i, a), some (j, b) => i = j ∧ a ≠ b

instance : DecidableRel (frAdj k) := fun u v => by
  rcases u with _ | ⟨i, a⟩ <;> rcases v with _ | ⟨j, b⟩ <;> unfold frAdj <;> infer_instance

def friendship : SimpleGraph (Option (Fin k × Fin 2)) where
  Adj := frAdj k
  symm := ⟨by
    rintro (_ | ⟨i, a⟩) (_ | ⟨j, b⟩) h <;> simp only [frAdj] at h ⊢ <;>
      first | trivial | exact h.elim | exact ⟨h.1.symm, Ne.symm h.2⟩⟩
  loopless := ⟨by rintro (_ | ⟨i, a⟩) h <;> simp [frAdj] at h⟩

instance : DecidableRel (friendship k).Adj := inferInstanceAs (DecidableRel (frAdj k))

theorem fr_deg_none : (friendship k).degree none = 2 * k := by
  rw [degree_eq_sum_ite, Fintype.sum_option]
  simp [friendship, frAdj, mul_comm]

theorem fr_deg_some (i : Fin k) (a : Fin 2) : (friendship k).degree (some (i, a)) = 2 := by
  rw [degree_eq_sum_ite, Fintype.sum_option, Fintype.sum_prod_type]
  fin_cases a <;> simp [friendship, frAdj, Fin.sum_univ_two]

theorem fr_degCls (f : friendship k →g K3) (x : Fin 3) :
    degCls f x = (if f none = x then 2 * k else 0) +
      ∑ i : Fin k, ((if f (some (i, 0)) = x then 2 else 0) + (if f (some (i, 1)) = x then 2 else 0)) := by
  rw [degCls_eq_sum, Fintype.sum_option, Fintype.sum_prod_type]
  simp only [fr_deg_none, fr_deg_some, Fin.sum_univ_two]

theorem two_of_three : ∀ c x u v : Fin 3, x ≠ c → u ≠ c → v ≠ c → u ≠ v →
    (if u = x then 2 else 0) + (if v = x then 2 else 0) = 2 := by decide

/-- **Observation `obs:friendship_exact`**: `γ(F_k,K₃) = k`. -/
theorem gamma_friendship : gamma (friendship k) K3 = k := by
  apply le_antisymm
  · let f : friendship k →g K3 := ⟨fun v => Option.elim v 2 (fun p => Fin.castSucc p.2), by
      rintro (_ | ⟨i, a⟩) (_ | ⟨j, b⟩) h <;> simp_all [friendship, frAdj, Fin.ext_iff] <;> omega⟩
    have hd : ∀ x : Fin 3, degCls f x = 2 * k := by
      intro x
      rw [fr_degCls]
      show (if (2 : Fin 3) = x then 2 * k else 0) + ∑ i : Fin k,
        ((if (0 : Fin 3) = x then 2 else 0) + (if (1 : Fin 3) = x then 2 else 0)) = 2 * k
      fin_cases x <;> simp [mul_comm]
    have := mu_eq_of_degCls f k (by rw [hd 0, hd 1, hd 2]; push_cast; simp only [max_self]; ring)
    calc gamma (friendship k) K3 ≤ mu f := gamma_le_mu f
      _ = k := by rw [this]
  · apply le_gamma
    intro f
    set c := f none
    have hl : ∀ i t, f (some (i, t)) ≠ c := fun i t =>
      f.map_rel (show (friendship k).Adj (some (i, t)) none by simp [friendship, frAdj])
    have hpair : ∀ i, f (some (i, 0)) ≠ f (some (i, 1)) := fun i =>
      f.map_rel (show (friendship k).Adj (some (i, 0)) (some (i, 1)) by simp [friendship, frAdj])
    have hD : ∀ x, x ≠ c → degCls f x = 2 * k := by
      intro x hx
      rw [fr_degCls, if_neg (Ne.symm hx), zero_add,
        sum_congr rfl (fun i _ => two_of_three c x _ _ hx (hl i 0) (hl i 1) (hpair i))]
      simp [mul_comm]
    have hDc : degCls f c = 2 * k := by
      rw [fr_degCls, if_pos rfl]
      simp [hl]
    obtain ⟨a, b, hab, hac, hbc⟩ := third_pair c
    have h := mu_ge_of_two_load f a b c hab hac hbc k (by
      rw [hD a hac, hD b hbc, hDc]; push_cast; ring)
    exact_mod_cast h

/-- **Observation `obs:friendship_exact`**: `|F_k,K₂| = k`. -/
theorem nhf_friendship_K2 : nhf (friendship k) (⊤ : SimpleGraph (Fin 2)) = k := by
  apply le_antisymm
  · let S : Finset (Sym2 (Option (Fin k × Fin 2))) :=
      univ.image fun i : Fin k => s(some (i, 0), some (i, 1))
    have hS : S.card = k := by
      rw [card_image_of_injective _ (by
        intro i j h
        simp only [Sym2.eq_iff, Option.some.injEq, Prod.mk.injEq] at h
        omega), card_univ, Fintype.card_fin]
    have h := nhf_le_card (G := friendship k) (H := (⊤ : SimpleGraph (Fin 2))) S
      ⟨⟨fun v => Option.elim v 0 (fun _ => 1), by
        rintro (_ | ⟨i, a⟩) (_ | ⟨j, b⟩) h <;> simp only [deleteEdges_adj] at h <;>
          simp_all [friendship, frAdj, S]
        obtain ⟨⟨rfl, hab⟩, hS⟩ := h
        fin_cases a <;> fin_cases b <;> simp_all [Sym2.eq_swap]⟩⟩
    rwa [hS] at h
  · apply le_nhf
    intro S ⟨g⟩
    -- each triangle contains a deleted edge
    have hT : ∀ i : Fin k, ∃ e ∈ S, e = s(none, some (i, 0)) ∨ e = s(none, some (i, 1)) ∨
        e = s(some (i, 0), some (i, 1)) := by
      intro i
      by_contra hcon
      push Not at hcon
      have adj : ∀ u v, (friendship k).Adj u v → s(u, v) ∉ S → g u ≠ g v := fun u v h hn =>
        g.map_rel (by rw [deleteEdges_adj]; exact ⟨h, hn⟩)
      have h1 := adj none (some (i, 0)) (by simp [friendship, frAdj])
        (fun h => (hcon _ h).1 rfl)
      have h2 := adj none (some (i, 1)) (by simp [friendship, frAdj])
        (fun h => (hcon _ h).2.1 rfl)
      have h3 := adj (some (i, 0)) (some (i, 1)) (by simp [friendship, frAdj])
        (fun h => (hcon _ h).2.2 rfl)
      revert h1 h2 h3
      generalize g none = x; generalize g (some (i, 0)) = y; generalize g (some (i, 1)) = z
      revert x y z; decide
    choose e heS heT using hT
    have hinj : Set.InjOn e (univ : Finset (Fin k)) := by
      intro i _ j _ hij
      have hi := heT i
      have hj := heT j
      rw [hij] at hi
      rcases hi with h | h | h <;> rcases hj with h' | h' | h' <;> rw [h] at h' <;>
        simp [Sym2.eq_iff] at h' <;> omega
    have := card_le_card_of_injOn e (fun i _ => heS i) hinj
    rw [card_univ, Fintype.card_fin] at this
    exact_mod_cast this

end friendship

/-! ### Wheels -/

section wheel

variable (j : ℕ)

/-- Rim size `R = 2j + 4`, written `2j + 1 + 3` to use the cycle-graph API. -/
abbrev R : ℕ := 2 * j + 1 + 3

/-- Wheel `W_{R+1}`: hub `none` joined to every vertex of the rim cycle `C_R`. -/
def whAdj : Option (Fin (R j)) → Option (Fin (R j)) → Prop
  | none, none => False
  | none, some _ => True
  | some _, none => True
  | some a, some b => (cycleGraph (R j)).Adj a b

instance : DecidableRel (whAdj j) := fun u v => by
  rcases u with _ | a <;> rcases v with _ | b <;> unfold whAdj <;> infer_instance

def wheel : SimpleGraph (Option (Fin (R j))) where
  Adj := whAdj j
  symm := ⟨by
    rintro (_ | a) (_ | b) h <;> simp only [whAdj] at h ⊢ <;> first | trivial | exact h.elim | exact h.symm⟩
  loopless := ⟨by rintro (_ | a) h <;> simp [whAdj] at h⟩

instance : DecidableRel (wheel j).Adj := inferInstanceAs (DecidableRel (whAdj j))

theorem wh_deg_none : (wheel j).degree none = R j := by
  rw [degree_eq_sum_ite, Fintype.sum_option]
  simp [wheel, whAdj]

theorem wh_deg_some (a : Fin (R j)) : (wheel j).degree (some a) = 3 := by
  rw [degree_eq_sum_ite, Fintype.sum_option]
  have h := (cycleGraph_degree_three_le (n := 2 * j + 1) (v := a))
  rw [degree_eq_sum_ite] at h
  have e1 : (wheel j).Adj (some a) none := trivial
  have e2 : ∀ b, (wheel j).Adj (some a) (some b) ↔ (cycleGraph (R j)).Adj a b := fun b => Iff.rfl
  rw [if_pos e1]
  simp only [e2]
  have : (∑ x : Fin (R j), if (cycleGraph (R j)).Adj a x then 1 else 0) = 2 := h
  omega

theorem wh_degCls (f : wheel j →g K3) (x : Fin 3) :
    degCls f x = (if f none = x then R j else 0) + ∑ a, if f (some a) = x then 3 else 0 := by
  rw [degCls_eq_sum, Fintype.sum_option]
  simp only [wh_deg_none, wh_deg_some]

theorem sum_mod_two (n : ℕ) : ∑ x ∈ range n, (if x % 2 = 0 then 1 else 0) = (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; split_ifs <;> omega

/-- **Observation `obs:wheel_gamma`**: for odd `n = 2j + 5 ≥ 5`, `γ(W_n,K₃) = n - 1`. -/
theorem gamma_wheel : gamma (wheel j) K3 = (R j : ℕ∞) := by
  apply le_antisymm
  · let f : wheel j →g K3 := ⟨fun v => Option.elim v 2 (fun a => ⟨a.val % 2, by omega⟩), by
      rintro (_ | a) (_ | b) h
      · exact absurd h (by simp [wheel, whAdj])
      · simp [Fin.ext_iff]; omega
      · simp [Fin.ext_iff]; omega
      · have := cycle_adj_val (k := 2 * j + 1) h
        simp only [top_adj, ne_eq, Option.elim_some, Fin.mk.injEq]
        omega⟩
    have e1 : ∀ t : Fin 3, (∑ a : Fin (R j), if f (some a) = t then 3 else 0) =
        3 * ∑ x ∈ range (R j), (if x % 2 = t.val then 1 else 0) := by
      intro t
      rw [mul_sum, ← Fin.sum_univ_eq_sum_range (fun x => 3 * if x % 2 = t.val then 1 else 0)]
      apply sum_congr rfl; intro a _
      have : (f (some a) = t) ↔ a.val % 2 = t.val := Fin.ext_iff
      simp only [this]; split_ifs <;> rfl
    have hsplit : ∀ n, ∑ x ∈ range n, (if x % 2 = 1 then 1 else 0) +
        ∑ x ∈ range n, (if x % 2 = 0 then 1 else 0) = n := by
      intro n; induction n with
      | zero => simp
      | succ n ih => rw [sum_range_succ, sum_range_succ]; split_ifs <;> omega
    have c0 : (∑ a : Fin (R j), if f (some a) = 0 then 3 else 0) = 3 * (j + 2) := by
      have hR : R j = 2 * j + 1 + 3 := rfl
      rw [e1 0]; simp only [Fin.val_zero]; rw [sum_mod_two]; omega
    have c1 : (∑ a : Fin (R j), if f (some a) = 1 then 3 else 0) = 3 * (j + 2) := by
      rw [e1 1]; simp only [Fin.val_one]
      have hR : R j = 2 * j + 1 + 3 := rfl
      have := hsplit (R j); have := sum_mod_two (R j); omega
    have hd0 := wh_degCls j f 0
    have hd1 := wh_degCls j f 1
    have hd2 := wh_degCls j f 2
    rw [c0] at hd0
    rw [c1] at hd1
    have h2s : (∑ a : Fin (R j), if f (some a) = 2 then 3 else 0) = 0 := by
      apply sum_eq_zero; intro a _
      have : f (some a) ≠ 2 := by
        simp only [f, ne_eq, Fin.ext_iff]; show ¬ (a.val % 2 = 2); omega
      simp [this]
    rw [h2s] at hd2
    have hf0 : f none = 2 := rfl
    simp only [hf0, show ((2 : Fin 3) = 0) = False by decide, show ((2 : Fin 3) = 1) = False by decide,
      if_false, if_true, zero_add, add_zero] at hd0 hd1 hd2
    have := mu_eq_of_degCls f (R j) (by
      rw [hd0, hd1, hd2]; simp only [max_def, R]; push_cast; split_ifs <;> omega)
    calc gamma (wheel j) K3 ≤ mu f := gamma_le_mu f
      _ = R j := by rw [this]
  · apply le_gamma
    intro f
    set c := f none
    have hr : ∀ a, f (some a) ≠ c := fun a =>
      f.map_rel (show (wheel j).Adj (some a) none by simp [wheel, whAdj])
    have hDc : degCls f c = R j := by
      rw [wh_degCls, if_pos rfl]; simp [hr]
    have htot := sum_degCls f
    rw [Fintype.sum_option, wh_deg_none] at htot
    simp only [wh_deg_some, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at htot
    obtain ⟨a, b, hab, hac, hbc⟩ := third_pair c
    have hsum := perm_sum a b c hab hac hbc (degCls f)
    have hR : R j = 2 * j + 1 + 3 := rfl
    have h := mu_ge_of_two_load f a b c hab hac hbc (R j) (by
      have : (degCls f a : ℤ) + degCls f b = 3 * R j := by
        have := htot.symm.trans hsum; rw [hDc] at this; push_cast; omega
      rw [hDc]; push_cast; omega)
    exact_mod_cast h

end wheel

/-! ### Complete tripartite graphs -/

section tripartite

variable (sz : Fin 3 → ℕ)

/-- `K_{sz 0, sz 1, sz 2}`: vertices `⟨i, x⟩` with `x < sz i`, adjacent iff parts differ. -/
def tri : SimpleGraph (Σ i : Fin 3, Fin (sz i)) := (⊤ : SimpleGraph (Fin 3)).comap Sigma.fst

instance : DecidableRel (tri sz).Adj := fun u v => inferInstanceAs (Decidable (u.1 ≠ v.1))

/-- Degree of a vertex in part `i`: the sum of the other two part sizes. -/
def degP (i : Fin 3) : ℕ := ∑ j, if i ≠ j then sz j else 0

theorem tri_deg (v : Σ i : Fin 3, Fin (sz i)) : (tri sz).degree v = degP sz v.1 := by
  rw [degree_eq_sum_ite, Fintype.sum_sigma, degP]
  apply sum_congr rfl; intro j _
  simp [tri]

theorem tri_degCls_of (f : tri sz →g K3) (col : Fin 3 → Fin 3) (hcol : Function.Injective col)
    (hf : ∀ v, f v = col v.1) (i : Fin 3) : degCls f (col i) = sz i * degP sz i := by
  rw [degCls_eq_sum, Fintype.sum_sigma]
  rw [sum_eq_single i]
  · simp [hf, tri_deg]
  · intro b _ hb; apply sum_eq_zero; intro x _
    simp [hf, hcol.ne hb]
  · simp

theorem tri_two_load (f : tri sz →g K3) (col : Fin 3 → Fin 3) (hcol : Function.Injective col)
    (hf : ∀ v, f v = col v.1) (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    load f s(col i, col j) = sz i * sz j := by
  have := two_load_eq f (col i) (col j) (col k) (hcol.ne hij) (hcol.ne hik) (hcol.ne hjk)
  rw [tri_degCls_of sz f col hcol hf, tri_degCls_of sz f col hcol hf,
    tri_degCls_of sz f col hcol hf] at this
  have key : (sz i * degP sz i : ℤ) + sz j * degP sz j - sz k * degP sz k = 2 * (sz i * sz j) := by
    simp only [degP, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hik hjk ⊢ <;> push_cast <;> ring
  have : (load f s(col i, col j) : ℤ) = sz i * sz j := by push_cast at this; linarith
  exact_mod_cast this

theorem four_colors' : ∀ a b c d : Fin 3, ¬(a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ d ≠ c) := by
  decide

theorem four_colors (a b c d : Fin 3) (h1 : a ≠ b) (h2 : c ≠ a) (h3 : c ≠ b) (h4 : d ≠ a)
    (h5 : d ≠ b) (h6 : d ≠ c) : False := four_colors' a b c d ⟨h1, h2, h3, h4, h5, h6⟩

theorem other_two : ∀ i : Fin 3, ∃ j k : Fin 3, j ≠ i ∧ k ≠ i ∧ j ≠ k := by decide

/-- **Observation `obs:multipartite_gamma`**: `γ(K_{p,q,r},K₃) = max(pq, pr, qr)` for
`p, q, r ≥ 1`. -/
theorem gamma_tri (hpos : ∀ i, 0 < sz i) :
    gamma (tri sz) K3 = ((max (max (sz 0 * sz 1) (sz 0 * sz 2)) (sz 1 * sz 2) : ℕ) : ℕ∞) := by
  have mu_of : ∀ f : tri sz →g K3, ∀ col : Fin 3 → Fin 3, Function.Injective col →
      (∀ v, f v = col v.1) → max (max (sz 0 * sz 1) (sz 0 * sz 2)) (sz 1 * sz 2) ≤ mu f := by
    intro f col hcol hf
    have l01 := tri_two_load sz f col hcol hf 0 1 2 (by decide) (by decide) (by decide)
    have l02 := tri_two_load sz f col hcol hf 0 2 1 (by decide) (by decide) (by decide)
    have l12 := tri_two_load sz f col hcol hf 1 2 0 (by decide) (by decide) (by decide)
    refine max_le (max_le ?_ ?_) ?_
    · rw [← l01]; exact load_le_mu f _
    · rw [← l02]; exact load_le_mu f _
    · rw [← l12]; exact load_le_mu f _
  apply le_antisymm
  · let f : tri sz →g K3 := ⟨Sigma.fst, fun h => h⟩
    have h0 := tri_degCls_of sz f id Function.injective_id (fun _ => rfl) 0
    have h1 := tri_degCls_of sz f id Function.injective_id (fun _ => rfl) 1
    have h2 := tri_degCls_of sz f id Function.injective_id (fun _ => rfl) 2
    simp only [id] at h0 h1 h2
    have := mu_eq_of_degCls f (max (max (sz 0 * sz 1) (sz 0 * sz 2)) (sz 1 * sz 2)) (by
      have dp0 : degP sz 0 = sz 1 + sz 2 := by simp [degP, Fin.sum_univ_three]
      have dp1 : degP sz 1 = sz 0 + sz 2 := by simp [degP, Fin.sum_univ_three]
      have dp2 : degP sz 2 = sz 0 + sz 1 := by simp [degP, Fin.sum_univ_three]
      rw [h0, h1, h2, dp0, dp1, dp2]
      push_cast
      have k1 : ((sz 0 : ℤ) * (sz 1 + sz 2) + sz 1 * (sz 0 + sz 2) - sz 2 * (sz 0 + sz 1)) =
          2 * (sz 0 * sz 1) := by ring
      have k2 : ((sz 0 : ℤ) * (sz 1 + sz 2) + sz 2 * (sz 0 + sz 1) - sz 1 * (sz 0 + sz 2)) =
          2 * (sz 0 * sz 2) := by ring
      have k3 : ((sz 1 : ℤ) * (sz 0 + sz 2) + sz 2 * (sz 0 + sz 1) - sz 0 * (sz 1 + sz 2)) =
          2 * (sz 1 * sz 2) := by ring
      rw [k1, k2, k3, ← mul_max_of_nonneg _ _ (by norm_num), ← mul_max_of_nonneg _ _ (by norm_num)])
    calc gamma (tri sz) K3 ≤ mu f := gamma_le_mu f
      _ = _ := by rw [this]
  · apply le_gamma
    intro f
    let rep : ∀ i : Fin 3, Σ i : Fin 3, Fin (sz i) := fun i => ⟨i, ⟨0, hpos i⟩⟩
    let col : Fin 3 → Fin 3 := fun i => f (rep i)
    have hadj : ∀ u v : Σ i : Fin 3, Fin (sz i), u.1 ≠ v.1 → f u ≠ f v := fun u v h => f.map_rel h
    have hcol : Function.Injective col := by
      intro i j h; by_contra hne; exact hadj (rep i) (rep j) hne h
    have hf : ∀ v, f v = col v.1 := by
      intro v
      by_contra hne
      obtain ⟨j, k, hj, hk, hjk⟩ := other_two v.1
      exact four_colors (f v) (col v.1) (col j) (col k) hne
        (hadj (rep j) v hj) (hadj (rep j) (rep v.1) hj)
        (hadj (rep k) v hk) (hadj (rep k) (rep v.1) hk) (hadj (rep k) (rep j) (Ne.symm hjk))
    exact_mod_cast mu_of f col hcol hf

/-- Table `tab:multipartite`: `max(pq,pr,qr)` is `6, 6, 12` for `K_{1,2,3}, K_{2,2,3}, K_{2,3,4}`. -/
theorem table_multipartite :
    [(1, 2, 3), (2, 2, 3), (2, 3, 4)].map (fun t : ℕ × ℕ × ℕ =>
      max (max (t.1 * t.2.1) (t.1 * t.2.2)) (t.2.1 * t.2.2)) = [6, 6, 12] := by decide

end tripartite

end NonHom
