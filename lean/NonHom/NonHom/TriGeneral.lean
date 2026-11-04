import NonHom.TriEquitable

/-!
# Triangular graphs `L(K_n)`: the Turán value is attained by some target of clique number `r`

**Theorem** (`nhf_triangular_general_target`). For every `n` and every `r ≥ 3` there is a graph
`K` with clique number exactly `r` (`K_{r+1}`-free and containing `K_r`) such that
`|L(K_n), K| = n·(C(n-1,2) - t(n-1,r))`.

This holds for every `n`, including odd `n` with `r ∣ n - 1` and `(n-1)/r` odd, where
`|L(K_n), K_r|` exceeds the Turán value by `r/2` (`tri_lower_parity`): the parity excess is
specific to the target `K_r`.

Construction. At every vertex `v` of `K_n` colour each other vertex `w` by `vidx v w mod r`,
where `vidx v` numbers the vertices `≠ v` by `0, …, n-2`; this is an equitable colouring `c_v`.
Let `K` (`triK`) be the graph on the edges of `K_n` in which `e ~ f` iff `e ≠ f`, they share a
vertex, and at every shared vertex `v` the other ends get different `c_v`-colours.
* `K` is `K_{r+1}`-free for `r ≥ 3`: `≥ 4` pairwise-intersecting edges form a star
  (`star_of_pairwise`), and inside the star at `v` adjacency forces distinct `c_v`-colours.
* The identity is a homomorphism from `L(K_n)` minus the monochromatic pairs to `K`, giving the
  upper bound (`nhf_line_triK_le`). The lower bound is `line_lower_clique`.
The final target is `K ⊕ K_r` (disjoint union), which also contains `K_r` when `n - 1 < r`.
-/

open SimpleGraph Finset

namespace NonHom

local notation "Kn" n => (⊤ : SimpleGraph (Fin n))

/-! ### Stars -/

/-- At least four pairwise-intersecting non-loop edges have a common vertex. -/
theorem star_of_pairwise {V : Type*} [DecidableEq V] (t : Finset (Sym2 V))
    (hnd : ∀ e ∈ t, ¬ e.IsDiag) (hpair : ∀ e ∈ t, ∀ f ∈ t, ∃ v, v ∈ e ∧ v ∈ f)
    (h4 : 4 ≤ t.card) : ∃ v, ∀ e ∈ t, v ∈ e := by
  obtain ⟨e, he⟩ : t.Nonempty := card_pos.mp (by omega)
  induction e using Sym2.ind with
  | _ a b =>
  by_contra hcon
  push Not at hcon
  have hab : a ≠ b := fun h => hnd _ he (by simp [h])
  obtain ⟨f, hf, haf⟩ := hcon a
  obtain ⟨g, hg, hbg⟩ := hcon b
  -- `f ∋ b`
  obtain ⟨w, hw1, hw2⟩ := hpair _ he f hf
  have hbf : b ∈ f := by
    rcases Sym2.mem_iff.mp hw1 with rfl | rfl
    · exact absurd hw2 haf
    · exact hw2
  obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.mp hbf
  -- `g ∋ a`
  obtain ⟨w', hw1', hw2'⟩ := hpair _ he g hg
  have hag : a ∈ g := by
    rcases Sym2.mem_iff.mp hw1' with rfl | rfl
    · exact hw2'
    · exact absurd hw2' hbg
  obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hag
  have hxa : x ≠ a := fun h => haf (by simp [h])
  have hya : y ≠ b := fun h => hbg (by simp [h])
  have hxb : x ≠ b := fun h => hnd _ hf (by simp [h])
  have hyb : y ≠ a := fun h => hnd _ hg (by simp [h])
  obtain ⟨u, hu1, hu2⟩ := hpair _ hf _ hg
  have hxy : x = y := by
    simp only [Sym2.mem_iff] at hu1 hu2
    grind
  subst hxy
  have h3 : ({s(a, b), s(b, x), s(a, x)} : Finset (Sym2 V)).card < t.card := by
    have := card_le_three (a := s(a, b)) (b := s(b, x)) (c := s(a, x))
    omega
  obtain ⟨h, ht, hnot⟩ := exists_mem_notMem_of_card_lt_card h3
  induction h using Sym2.ind with
  | _ p q =>
  have hpq : p ≠ q := fun h => hnd _ ht (by simp [h])
  obtain ⟨u1, hu1, hu1'⟩ := hpair _ ht _ he
  obtain ⟨u2, hu2, hu2'⟩ := hpair _ ht _ hf
  obtain ⟨u3, hu3, hu3'⟩ := hpair _ ht _ hg
  simp only [Sym2.mem_iff] at hu1 hu1' hu2 hu2' hu3 hu3'
  apply hnot
  simp only [mem_insert, mem_singleton, Sym2.eq_iff]
  grind

/-! ### The colourings `c_v` and the target `K` -/

/-- Number of `w` among the vertices `≠ v`, in `[0, n - 1)`. -/
def vidx {n : ℕ} (v w : Fin n) : ℕ := if w.val < v.val then w.val else w.val - 1

/-- The equitable colouring `c_v` of the vertices `≠ v`. -/
def vcol {n r : ℕ} (hr : 0 < r) (v w : Fin n) : Fin r := ⟨vidx v w % r, Nat.mod_lt _ hr⟩

/-- `c_v` read on edges: the colour of the other end (junk on edges not at `v`). -/
def ecol {n r : ℕ} (hr : 0 < r) (v : Fin n) (e : Sym2 (Fin n)) : Fin r :=
  Sym2.lift ⟨fun a b => if a = v then vcol hr v b else if b = v then vcol hr v a else ⟨0, hr⟩,
    fun a b => by
      by_cases ha : a = v <;> by_cases hb : b = v <;> simp [ha, hb]⟩ e

theorem ecol_mk {n r : ℕ} (hr : 0 < r) (v w : Fin n) : ecol hr v s(v, w) = vcol hr v w := by
  simp [ecol]

/-- The target `K` on the edges of `K_n`. -/
def triK (n r : ℕ) (hr : 0 < r) : SimpleGraph (Kn n).edgeSet where
  Adj e f := e ≠ f ∧ (∃ v, v ∈ (e : Sym2 (Fin n)) ∧ v ∈ (f : Sym2 (Fin n))) ∧
    ∀ v, v ∈ (e : Sym2 (Fin n)) → v ∈ (f : Sym2 (Fin n)) → ecol hr v e.1 ≠ ecol hr v f.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, let ⟨v, h1, h2⟩ := h.2.1; ⟨v, h2, h1⟩,
    fun v h1 h2 => (h.2.2 v h2 h1).symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- **`K` is `K_{r+1}`-free** for `r ≥ 3`. -/
theorem triK_cliqueFree (n r : ℕ) (hr3 : 3 ≤ r) (hr : 0 < r) :
    (triK n r hr).CliqueFree (r + 1) := by
  classical
  intro t ht
  have hadj : ∀ e ∈ t, ∀ f ∈ t, e ≠ f → (triK n r hr).Adj e f :=
    fun e he f hf hne => ht.1 (mem_coe.mpr he) (mem_coe.mpr hf) hne
  obtain ⟨v, hv⟩ : ∃ v, ∀ e ∈ t, v ∈ (e : Sym2 (Fin n)) := by
    obtain ⟨v, hv⟩ := star_of_pairwise (t.map (Function.Embedding.subtype _))
      (by
        intro e he
        obtain ⟨e, -, rfl⟩ := mem_map.mp he
        exact (Kn n).not_isDiag_of_mem_edgeSet e.2)
      (by
        intro e' he' f' hf'
        obtain ⟨e, he, rfl⟩ := mem_map.mp he'
        obtain ⟨f, hf, rfl⟩ := mem_map.mp hf'
        by_cases hef : e = f
        · subst hef
          obtain ⟨z, hz⟩ := e
          induction z using Sym2.ind with
          | _ a b => exact ⟨a, by simp, by simp⟩
        · exact (hadj e he f hf hef).2.1)
      (by rw [card_map, ht.2]; omega)
    exact ⟨v, fun e he => hv _ (mem_map_of_mem _ he)⟩
  have hinj : Set.InjOn (fun e : (Kn n).edgeSet => ecol hr v e.1) (t : Set _) := by
    intro e he f hf h
    by_contra hne
    exact (hadj e he f hf hne).2.2 v (hv e he) (hv f hf) h
  have := card_le_card_of_injOn (t := (univ : Finset (Fin r))) _
    (fun _ _ => mem_coe.mpr (mem_univ _)) hinj
  rw [card_univ, Fintype.card_fin, ht.2] at this
  omega

/-! ### Counting: `c_v` is equitable -/

theorem dcol_ecol (n r : ℕ) (hr : 0 < r) (v : Fin n) (i : Fin r) :
    dcol (fun e : (Kn n).edgeSet => ecol hr v e.1) v i =
      (univ.filter fun w : Fin n => w ≠ v ∧ vidx v w % r = i.val).card := by
  unfold dcol
  symm
  apply card_bij (fun u hu => (⟨⟨s(v, u), by
      simp only [mem_filter, mem_univ, true_and] at hu
      exact (top_adj v u).mpr (Ne.symm hu.1)⟩, Sym2.mem_mk_left v u⟩ : At (Kn n) v))
  · intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu ⊢
    rw [ecol_mk]; exact Fin.ext hu.2
  · intro u hu u' hu' h
    have h' := congrArg (fun z : At (Kn n) v => (z.1 : Sym2 (Fin n))) h
    exact Sym2.congr_right.mp h'
  · rintro ⟨⟨e, he⟩, hv⟩ hcol
    simp only [mem_filter, mem_univ, true_and] at hcol
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp hv
    refine ⟨u, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨fun h => ((SimpleGraph.mem_edgeSet _).mp he).ne h.symm, ?_⟩
    rw [ecol_mk] at hcol
    exact congrArg Fin.val hcol

theorem card_vidx (n r : ℕ) (v : Fin n) (i : ℕ) :
    (univ.filter fun w : Fin n => w ≠ v ∧ vidx v w % r = i).card =
      ((range (n - 1)).filter fun x => x % r = i).card := by
  apply card_bij (fun w _ => vidx v w)
  · intro w hw
    simp only [mem_filter, mem_univ, true_and, mem_range] at hw ⊢
    have hw' : w.val ≠ v.val := fun h => hw.1 (Fin.ext h)
    refine ⟨?_, hw.2⟩
    have := w.isLt; have := v.isLt
    unfold vidx; split_ifs <;> omega
  · intro w hw w' hw' h
    simp only [mem_filter, mem_univ, true_and] at hw hw'
    have h1 : w.val ≠ v.val := fun h => hw.1 (Fin.ext h)
    have h2 : w'.val ≠ v.val := fun h => hw'.1 (Fin.ext h)
    apply Fin.ext
    unfold vidx at h; split_ifs at h <;> omega
  · intro x hx
    simp only [mem_filter, mem_range] at hx
    refine ⟨⟨if x < v.val then x else x + 1, by split_ifs <;> omega⟩, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and, ne_eq, Fin.ext_iff]
      have hvx : vidx v ⟨if x < v.val then x else x + 1, by split_ifs <;> omega⟩ = x := by
        unfold vidx; split_ifs <;> simp_all; omega
      refine ⟨by split_ifs <;> omega, by rw [hvx]; exact hx.2⟩
    · unfold vidx; split_ifs <;> simp_all; omega

theorem dcol_ecol_bounds (n r : ℕ) (hr : 0 < r) (v : Fin n) (i : Fin r) :
    (n - 1) / r ≤ dcol (fun e : (Kn n).edgeSet => ecol hr v e.1) v i ∧
      dcol (fun e : (Kn n).edgeSet => ecol hr v e.1) v i ≤ (n - 1) / r + 1 := by
  rw [dcol_ecol, card_vidx]
  have hc := Nat.count_modEq_card (n - 1) hr i.val
  rw [Nat.count_eq_card_filter_range] at hc
  have e : ((range (n - 1)).filter fun x => x % r = i.val) =
      (range (n - 1)).filter fun x => x ≡ i.val [MOD r] := by
    apply filter_congr; intro x _
    rw [Nat.ModEq, Nat.mod_eq_of_lt i.isLt]
  rw [e, hc]
  split_ifs <;> omega

/-- Monochromatic pairs at `v`: `C(n-1,2) - t(n-1,r)` of them. -/
theorem card_mono_ecol (n r : ℕ) (hr : 0 < r) (v : Fin n)
    [Fintype ((⊤ : SimpleGraph (At (Kn n) v)) \
      (⊤ : SimpleGraph (Fin r)).comap (fun e => ecol hr v e.1.1)).edgeSet] :
    ((⊤ : SimpleGraph (At (Kn n) v)) \
      (⊤ : SimpleGraph (Fin r)).comap (fun e => ecol hr v e.1.1)).edgeFinset.card =
      (n - 1).choose 2 - turanNumber (n - 1) r := by
  have hreg := top_regular n
  rw [card_mono_r hreg (fun e : (Kn n).edgeSet => ecol hr v e.1) v]
  have hb := dcol_ecol_bounds n r hr v
  have h1 := sum_choose_near _ hb
  rw [sum_dcol hreg] at h1
  have hn1 : n - 1 = (n - 1) / r * r + (n - 1) % r := (Nat.div_add_mod' _ _).symm
  set q := (n - 1) / r
  have h2 := turan_add_eq r ((n - 1) % r) (Nat.mod_lt _ hr) q
  rw [← hn1] at h2
  have h3 : q * (n - 1) = r * (q * q) + q * ((n - 1) % r) := by
    conv_lhs => rw [hn1]
    ring
  omega

/-- **Upper bound.** `|L(K_n), K| ≤ n·(C(n-1,2) - t(n-1,r))`. -/
theorem nhf_line_triK_le (n r : ℕ) (hr : 0 < r) :
    nhf (Kn n).lineGraph (triK n r hr) ≤
      ((n * ((n - 1).choose 2 - turanNumber (n - 1) r) : ℕ) : ℕ∞) := by
  classical
  let S : Finset (Sym2 (Kn n).edgeSet) :=
    ((Kn n).lineGraph ⊓ SimpleGraph.fromRel fun a b => ¬ (triK n r hr).Adj a b).edgeFinset
  have hhom : Nonempty ((Kn n).lineGraph.deleteEdges ↑S →g triK n r hr) := by
    refine ⟨⟨id, fun {a b} h => ?_⟩⟩
    rw [deleteEdges_adj] at h
    by_contra hn
    apply h.2
    simp only [S, coe_edgeFinset]
    exact ⟨h.1, h.1.ne, Or.inl hn⟩
  refine (nhf_le_card S hhom).trans ?_
  norm_cast
  let Mv : ∀ v, SimpleGraph (At (Kn n) v) := fun v =>
    (⊤ : SimpleGraph (At (Kn n) v)) \ (⊤ : SimpleGraph (Fin r)).comap (fun e => ecol hr v e.1.1)
  let ι : ∀ v, Sym2 (At (Kn n) v) → Sym2 (Kn n).edgeSet := fun v => Sym2.map Subtype.val
  have hcover : S ⊆ univ.biUnion fun v => (Mv v).edgeFinset.image (ι v) := by
    intro z hz
    simp only [S, mem_edgeFinset] at hz
    induction z using Sym2.ind with
    | _ a b =>
      obtain ⟨hL, -, hcol⟩ := hz
      have hnK : ¬ (triK n r hr).Adj a b := hcol.elim id (fun h h' => h h'.symm)
      rw [lineGraph_adj_iff_exists] at hL
      obtain ⟨hne, v0, hva0, hvb0⟩ := hL
      have : ∃ v, v ∈ (a : Sym2 (Fin n)) ∧ v ∈ (b : Sym2 (Fin n)) ∧
          ecol hr v a.1 = ecol hr v b.1 := by
        by_contra hc
        push Not at hc
        exact hnK ⟨hne, ⟨v0, hva0, hvb0⟩, fun v h1 h2 => hc v h1 h2⟩
      obtain ⟨v, hva, hvb, hcab⟩ := this
      rw [mem_biUnion]
      refine ⟨v, mem_univ _, mem_image.mpr ⟨s(⟨a, hva⟩, ⟨b, hvb⟩), ?_, rfl⟩⟩
      rw [mem_edgeFinset]
      show (Mv v).Adj ⟨a, hva⟩ ⟨b, hvb⟩
      exact ⟨fun h => hne (congrArg Subtype.val h), fun h => h hcab⟩
  calc S.card ≤ (univ.biUnion fun v => (Mv v).edgeFinset.image (ι v)).card := card_le_card hcover
    _ ≤ ∑ v, ((Mv v).edgeFinset.image (ι v)).card := card_biUnion_le
    _ ≤ ∑ v, (Mv v).edgeFinset.card := sum_le_sum fun v _ => card_image_le
    _ = _ := by
        rw [sum_congr rfl (fun v _ => card_mono_ecol n r hr v), sum_const, card_univ,
          Fintype.card_fin, smul_eq_mul]

/-- **Exact value for `K`.** For `r ≥ 3`, `|L(K_n), K| = n·(C(n-1,2) - t(n-1,r))`. -/
theorem nhf_line_triK (n r : ℕ) (hr3 : 3 ≤ r) (hr : 0 < r) :
    nhf (Kn n).lineGraph (triK n r hr) =
      ((n * ((n - 1).choose 2 - turanNumber (n - 1) r) : ℕ) : ℕ∞) := by
  classical
  apply le_antisymm (nhf_line_triK_le n r hr)
  have h := line_lower_clique (top_regular n) (triK_cliqueFree n r hr3 hr)
  rwa [Fintype.card_fin] at h

/-- For `r < n`, `K` itself contains `K_r` (the star at the last vertex). -/
def triK_top_hom (n r : ℕ) (hr : 0 < r) (hrn : r < n) : (⊤ : SimpleGraph (Fin r)) →g triK n r hr where
  toFun i := ⟨s(⟨n - 1, by omega⟩, ⟨i.val, by omega⟩), by
    rw [mem_edgeSet, top_adj]; intro h; have := congrArg Fin.val h; simp at this; omega⟩
  map_rel' {i j} hij := by
    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hi := i.isLt; have hj := j.isLt
    refine ⟨?_, ⟨⟨n - 1, by omega⟩, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩, ?_⟩
    · intro h
      have h' := congrArg (fun z : (Kn n).edgeSet => (z : Sym2 (Fin n))) h
      simp only [Sym2.eq_iff, Fin.ext_iff] at h'
      omega
    · intro v hv1 hv2
      have hv : v = ⟨n - 1, by omega⟩ := by
        simp only [Sym2.mem_iff, Fin.ext_iff] at hv1 hv2 ⊢
        omega
      subst hv
      rw [ecol_mk, ecol_mk]
      simp only [vcol, vidx, ne_eq, Fin.mk.injEq]
      rw [ite_eq_left (show i.val < n - 1 by omega), ite_eq_left (show j.val < n - 1 by omega),
        Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
      exact hij'

/-! ### Adding a disjoint `K_r` -/

theorem cliqueFree_sum {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {m : ℕ}
    (hG : G.CliqueFree m) (hH : H.CliqueFree m) : (G ⊕g H).CliqueFree m := by
  classical
  intro t ht
  have hadj : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → (G ⊕g H).Adj x y :=
    fun x hx y hy hne => ht.1 (mem_coe.mpr hx) (mem_coe.mpr hy) hne
  by_cases hl : ∃ a, Sum.inl a ∈ t
  · obtain ⟨a, ha⟩ := hl
    have hall : ∀ x ∈ t, x ∈ Set.range (Sum.inl : V → V ⊕ W) := by
      intro x hx
      rcases x with b | b
      · exact ⟨b, rfl⟩
      · exact absurd (hadj _ ha _ hx (by simp)) (by simp)
    apply hG (t.preimage Sum.inl Sum.inl_injective.injOn)
    refine ⟨fun x hx y hy hxy => ?_, ?_⟩
    · have := hadj _ (mem_preimage.mp hx) _ (mem_preimage.mp hy) (by simpa using hxy)
      simpa using this
    · rw [card_preimage, filter_true_of_mem hall, ht.2]
  · push Not at hl
    have hall : ∀ x ∈ t, x ∈ Set.range (Sum.inr : W → V ⊕ W) := by
      intro x hx
      rcases x with b | b
      · exact absurd hx (hl b)
      · exact ⟨b, rfl⟩
    apply hH (t.preimage Sum.inr Sum.inr_injective.injOn)
    refine ⟨fun x hx y hy hxy => ?_, ?_⟩
    · have := hadj _ (mem_preimage.mp hx) _ (mem_preimage.mp hy) (by simpa using hxy)
      simpa using this
    · rw [card_preimage, filter_true_of_mem hall, ht.2]

/-- **Triangular graphs: the Turán value is attained by a target of clique number `r`.**
For every `n` and every `r ≥ 3` there is a graph `K` that is `K_{r+1}`-free, contains `K_r`,
and satisfies `|L(K_n), K| = n·(C(n-1,2) - t(n-1,r))`. -/
theorem nhf_triangular_general_target (n r : ℕ) (hr : 3 ≤ r) :
    ∃ K : SimpleGraph ((Kn n).edgeSet ⊕ Fin r), K.CliqueFree (r + 1) ∧
      Nonempty ((⊤ : SimpleGraph (Fin r)) →g K) ∧
      nhf (Kn n).lineGraph K = ((n * ((n - 1).choose 2 - turanNumber (n - 1) r) : ℕ) : ℕ∞) := by
  classical
  have hr0 : 0 < r := by omega
  have hcf : (triK n r hr0 ⊕g (⊤ : SimpleGraph (Fin r))).CliqueFree (r + 1) :=
    cliqueFree_sum (triK_cliqueFree n r hr hr0)
      (cliqueFree_of_card_lt (by rw [Fintype.card_fin]; omega))
  refine ⟨triK n r hr0 ⊕g (⊤ : SimpleGraph (Fin r)), hcf, ⟨Embedding.sumInr.toHom⟩, ?_⟩
  apply le_antisymm
  · exact (nhf_le_of_hom_target Embedding.sumInl.toHom).trans (nhf_line_triK_le n r hr0)
  · have h := line_lower_clique (top_regular n) hcf
    rwa [Fintype.card_fin] at h

/-- Variant with `K` on the edge set of `K_n` itself, for `r < n`. -/
theorem nhf_triangular_general_target_edges (n r : ℕ) (hr : 3 ≤ r) (hrn : r < n) :
    ∃ K : SimpleGraph (Kn n).edgeSet, K.CliqueFree (r + 1) ∧
      Nonempty ((⊤ : SimpleGraph (Fin r)) →g K) ∧
      nhf (Kn n).lineGraph K = ((n * ((n - 1).choose 2 - turanNumber (n - 1) r) : ℕ) : ℕ∞) :=
  ⟨triK n r (by omega), triK_cliqueFree n r hr _, ⟨triK_top_hom n r _ hrn⟩, nhf_line_triK n r hr _⟩

end NonHom
