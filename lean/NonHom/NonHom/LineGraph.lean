import NonHom.OpenProblems

/-!
# Sage result 2 (`open_problems/sage_a1_5/README.md`): line graphs of regular graphs

**Lower bound (formalized here).** If `G` is `d`-regular on `n` vertices and `H` is triangle-free,
then `|L(G), H| ≥ n·(C(d,2) - ⌊d²/4⌋) = n·⌊(d-1)²/4⌋`.

The edges at a vertex `v` form a clique `Q_v ≅ K_d` in `L(G)`; the cliques are edge-disjoint; and
the kept part of each `Q_v` is triangle-free, so by Mantel it keeps at most `⌊d²/4⌋` edges.

The matching upper bound in the README relies on Petersen's 2-factor theorem, König's theorem,
or a perfect matching, none of which is used here.
-/

open SimpleGraph Finset

namespace NonHom

variable {V W : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The edges of `G` at `v`. -/
abbrev At (G : SimpleGraph V) (v : V) := {e : G.edgeSet // v ∈ (e : Sym2 V)}

theorem card_At {d : ℕ} (hreg : G.IsRegularOfDegree d) (v : V) : Fintype.card (At G v) = d := by
  rw [← hreg.degree_eq v, ← card_incidenceFinset_eq_degree, incidenceFinset_eq_filter]
  rw [← Fintype.card_coe]
  exact Fintype.card_congr
    { toFun := fun e => ⟨e.1.1, by simp [e.2, mem_edgeFinset.mpr e.1.2]⟩
      invFun := fun e => ⟨⟨e.1, mem_edgeFinset.mp (mem_filter.mp e.2).1⟩, (mem_filter.mp e.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem line_lower {d : ℕ} (hreg : G.IsRegularOfDegree d) {H : SimpleGraph W} [DecidableEq W]
    (hH : H.CliqueFree 3) :
    ((Fintype.card V * (d.choose 2 - d ^ 2 / 4) : ℕ) : ℕ∞) ≤ nhf G.lineGraph H := by
  classical
  apply le_nhf
  intro S ⟨g⟩
  set K := G.lineGraph.deleteEdges ↑S
  have hK : K.CliqueFree 3 := cliqueFree_of_hom g hH
  -- the kept part of each clique
  let Kv : ∀ v, SimpleGraph (At G v) := fun v => K.comap (fun e => e.1)
  have hKv : ∀ v, (Kv v).CliqueFree 3 := fun v =>
    cliqueFree_of_hom (⟨fun e => e.1, fun h => h⟩ : Kv v →g K) hK
  let D : ∀ v, Finset (Sym2 (At G v)) := fun v =>
    (⊤ : SimpleGraph (At G v)).edgeFinset \ (Kv v).edgeFinset
  have hD : ∀ v, d.choose 2 - d ^ 2 / 4 ≤ (D v).card := by
    intro v
    have h1 := (hKv v).card_edgeFinset_le
    rw [card_At hreg, turanNumber_two] at h1
    have h1' : (Kv v).edgeFinset.card ≤ d ^ 2 / 4 := by convert h1
    have h2 : (D v).card = (⊤ : SimpleGraph (At G v)).edgeFinset.card - (Kv v).edgeFinset.card :=
      card_sdiff_of_subset (edgeFinset_mono le_top)
    rw [card_edgeFinset_top_eq_card_choose_two, card_At hreg] at h2
    omega
  let ι : ∀ v, Sym2 (At G v) → Sym2 G.edgeSet := fun v => Sym2.map Subtype.val
  have hιinj : ∀ v, Function.Injective (ι v) := fun v => Sym2.map.injective Subtype.val_injective
  -- images lie in `S`
  have hsub : ∀ v, (D v).image (ι v) ⊆ S := by
    intro v z hz
    obtain ⟨z, hzD, rfl⟩ := mem_image.mp hz
    simp only [D, mem_sdiff, mem_edgeFinset] at hzD
    obtain ⟨htop, hnot⟩ := hzD
    induction z using Sym2.ind with
    | _ a b =>
      have hab : a ≠ b := htop
      by_contra hS
      apply hnot
      show K.Adj a.1 b.1
      rw [deleteEdges_adj, lineGraph_adj_iff_exists]
      exact ⟨⟨fun h => hab (Subtype.ext h), v, a.2, b.2⟩, hS⟩
  -- images for different vertices are disjoint
  have hdisj : ∀ v ∈ (univ : Finset V), ∀ w ∈ (univ : Finset V), v ≠ w →
      Disjoint ((D v).image (ι v)) ((D w).image (ι w)) := by
    intro v _ w _ hvw
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨z₁, hz₁, rfl⟩ := mem_image.mp hz
    obtain ⟨z₂, -, hz₂⟩ := mem_image.mp hz'
    simp only [D, mem_sdiff, mem_edgeFinset] at hz₁
    induction z₁ using Sym2.ind with
    | _ a b =>
      induction z₂ using Sym2.ind with
      | _ a' b' =>
        have hab : a ≠ b := hz₁.1
        simp only [ι, Sym2.map_mk, Sym2.eq_iff] at hz₂
        have hw : w ∈ (a.1 : Sym2 V) ∧ w ∈ (b.1 : Sym2 V) := by
          rcases hz₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨h1 ▸ a'.2, h2 ▸ b'.2⟩
          · exact ⟨h2 ▸ b'.2, h1 ▸ a'.2⟩
        have e1 := (Sym2.mem_and_mem_iff hvw).mp ⟨a.2, hw.1⟩
        have e2 := (Sym2.mem_and_mem_iff hvw).mp ⟨b.2, hw.2⟩
        exact hab (Subtype.ext (Subtype.ext (e1.trans e2.symm)))
  have hbig : (univ.biUnion fun v => (D v).image (ι v)) ⊆ S := biUnion_subset.mpr fun v _ => hsub v
  have hcard := card_le_card hbig
  rw [card_biUnion hdisj] at hcard
  have : ∑ v : V, (d.choose 2 - d ^ 2 / 4) ≤ ∑ v : V, ((D v).image (ι v)).card := by
    apply sum_le_sum; intro v _
    rw [card_image_of_injective _ (hιinj v)]; exact hD v
  rw [sum_const, card_univ, smul_eq_mul] at this
  exact_mod_cast this.trans hcard

/-- `C(d,2) - ⌊d²/4⌋ = ⌊(d-1)²/4⌋`. -/
theorem choose_two_sub (d : ℕ) : d.choose 2 - d ^ 2 / 4 = (d - 1) ^ 2 / 4 := by
  rcases Nat.even_or_odd' d with ⟨t, rfl | rfl⟩
  · rcases t with _ | t
    · simp
    · rw [Nat.choose_two_right]
      have e1 : 2 * (t + 1) * (2 * (t + 1) - 1) / 2 = (t + 1) * (2 * t + 1) := by
        rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
      have e2 : (2 * (t + 1)) ^ 2 / 4 = (t + 1) * (t + 1) := by
        rw [show (2 * (t + 1)) ^ 2 = 4 * ((t + 1) * (t + 1)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
      have e3 : (2 * (t + 1) - 1) ^ 2 / 4 = t * (t + 1) := by
        rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega,
          show (2 * t + 1) ^ 2 = 4 * (t * (t + 1)) + 1 by ring]
        omega
      rw [e1, e2, e3]
      have : (t + 1) * (2 * t + 1) = (t + 1) * (t + 1) + t * (t + 1) := by ring
      omega
  · rw [Nat.choose_two_right]
    have e1 : (2 * t + 1) * (2 * t + 1 - 1) / 2 = (2 * t + 1) * t := by
      rw [show 2 * t + 1 - 1 = 2 * t by omega, show (2 * t + 1) * (2 * t) = 2 * ((2 * t + 1) * t) by ring,
        Nat.mul_div_cancel_left _ (by norm_num)]
    have e2 : (2 * t + 1) ^ 2 / 4 = t * (t + 1) := by
      rw [show (2 * t + 1) ^ 2 = 4 * (t * (t + 1)) + 1 by ring]; omega
    have e3 : (2 * t + 1 - 1) ^ 2 / 4 = t * t := by
      rw [show 2 * t + 1 - 1 = 2 * t by omega, show (2 * t) ^ 2 = 4 * (t * t) by ring,
        Nat.mul_div_cancel_left _ (by norm_num)]
    rw [e1, e2, e3]
    have : (2 * t + 1) * t = t * (t + 1) + t * t := by ring
    omega

/-- **Sage result 2, lower bound**: `|L(G), H| ≥ n·⌊(d-1)²/4⌋`. For cubic `G` this is `n`. -/
theorem line_lower' {d : ℕ} (hreg : G.IsRegularOfDegree d) {H : SimpleGraph W} [DecidableEq W]
    (hH : H.CliqueFree 3) :
    ((Fintype.card V * ((d - 1) ^ 2 / 4) : ℕ) : ℕ∞) ≤ nhf G.lineGraph H := by
  rw [← choose_two_sub]; exact line_lower hreg hH

/-! ### Upper bound from a balanced 2-edge-colouring -/

/-- Number of ordered pairs of `T` with different colours. -/
theorem card_diff_pairs {T : Type*} [Fintype T] [DecidableEq T] (c : T → Fin 2) :
    (univ.filter fun p : T × T => c p.1 ≠ c p.2).card =
      2 * ((univ.filter fun x => c x = 0).card * (univ.filter fun x => c x = 1).card) := by
  rw [card_filter, Fintype.sum_prod_type]
  have h : ∀ x : T, (∑ y : T, if c x ≠ c y then 1 else 0) =
      if c x = 0 then (univ.filter fun y => c y = 1).card else (univ.filter fun y => c y = 0).card := by
    intro x
    rw [card_filter, card_filter]
    have hx : c x = 0 ∨ c x = 1 := by omega
    rcases hx with hx | hx <;> simp only [hx] <;> apply sum_congr rfl <;> intro y _ <;>
      have hy : c y = 0 ∨ c y = 1 := (by omega) <;> rcases hy with hy | hy <;> simp [hy]
  rw [sum_congr rfl fun x _ => h x, ← sum_filter_add_sum_filter_not univ (fun x => c x = 0)]
  rw [sum_congr rfl (fun x hx => if_pos (mem_filter.mp hx).2),
    sum_congr rfl (fun x hx => if_neg (mem_filter.mp hx).2), sum_const, sum_const, smul_eq_mul,
    smul_eq_mul]
  have : (univ.filter fun x => ¬ c x = 0) = univ.filter fun x => c x = 1 := by
    ext x; simp only [mem_filter, mem_univ, true_and]; omega
  rw [this]; ring

/-- If the colouring `c` of `E(G)` is balanced at every vertex (colour-0 count `⌊d/2⌋` or
`⌈d/2⌉`), then `|L(G), K₂| ≤ n·(C(d,2) - ⌊d²/4⌋)`. -/
theorem line_upper {d : ℕ} (hreg : G.IsRegularOfDegree d) (c : G.edgeSet → Fin 2)
    (hbal : ∀ v, (univ.filter fun e : At G v => c e.1 = 0).card = d / 2 ∨
      (univ.filter fun e : At G v => c e.1 = 0).card = (d + 1) / 2) :
    nhf G.lineGraph (⊤ : SimpleGraph (Fin 2)) ≤ ((Fintype.card V * (d.choose 2 - d ^ 2 / 4) : ℕ) : ℕ∞) := by
  classical
  -- monochromatic line-graph edges
  let Mono : SimpleGraph G.edgeSet := G.lineGraph ⊓ SimpleGraph.fromRel fun a b => c a = c b
  let S : Finset (Sym2 G.edgeSet) := Mono.edgeFinset
  have hhom : Nonempty (G.lineGraph.deleteEdges ↑S →g (⊤ : SimpleGraph (Fin 2))) := by
    refine ⟨⟨c, fun {a b} h => ?_⟩⟩
    rw [deleteEdges_adj] at h
    intro hab
    apply h.2
    simp only [S, coe_edgeFinset, Set.mem_ofPred_eq]
    show Mono.Adj a b
    exact ⟨h.1, h.1.ne, Or.inl hab⟩
  refine (nhf_le_card S hhom).trans ?_
  norm_cast
  -- per-vertex monochromatic pairs
  let Mv : ∀ v, SimpleGraph (At G v) := fun v =>
    (⊤ : SimpleGraph (At G v)) \ (⊤ : SimpleGraph (Fin 2)).comap (fun e => c e.1)
  let ι : ∀ v, Sym2 (At G v) → Sym2 G.edgeSet := fun v => Sym2.map Subtype.val
  have hcover : S ⊆ univ.biUnion fun v => (Mv v).edgeFinset.image (ι v) := by
    intro z hz
    simp only [S, mem_edgeFinset] at hz
    induction z using Sym2.ind with
    | _ a b =>
      obtain ⟨hL, -, hcol⟩ := hz
      rw [lineGraph_adj_iff_exists] at hL
      obtain ⟨hne, v, hva, hvb⟩ := hL
      have hcab : c a = c b := hcol.elim id Eq.symm
      rw [mem_biUnion]
      refine ⟨v, mem_univ _, mem_image.mpr ⟨s(⟨a, hva⟩, ⟨b, hvb⟩), ?_, rfl⟩⟩
      rw [mem_edgeFinset]
      show (Mv v).Adj ⟨a, hva⟩ ⟨b, hvb⟩
      exact ⟨fun h => hne (congrArg Subtype.val h), fun h => h hcab⟩
  have hcount : ∀ v, (Mv v).edgeFinset.card = d.choose 2 - d ^ 2 / 4 := by
    intro v
    set a := (univ.filter fun e : At G v => c e.1 = 0).card
    set b := (univ.filter fun e : At G v => c e.1 = 1).card
    have hab : a + b = d := by
      have h := card_filter_add_card_filter_not (s := (univ : Finset (At G v)))
        (fun e : At G v => c e.1 = 0)
      have hnot : (univ.filter fun e : At G v => ¬ c e.1 = 0) = univ.filter fun e => c e.1 = 1 := by
        ext e; simp only [mem_filter, mem_univ, true_and]; omega
      rw [hnot, card_univ, card_At hreg v] at h
      exact h
    let Dv : SimpleGraph (At G v) := (⊤ : SimpleGraph (Fin 2)).comap (fun e => c e.1)
    have hD : 2 * Dv.edgeFinset.card = 2 * (a * b) := by
      rw [two_mul_card_edgeFinset, ← card_diff_pairs (fun e : At G v => c e.1)]
      congr 1
    have hDle : Dv ≤ ⊤ := le_top
    have hsd : (Mv v).edgeFinset = (⊤ : SimpleGraph (At G v)).edgeFinset \ Dv.edgeFinset := by
      ext z; simp [Mv, Dv, edgeSet_sdiff]
    rw [hsd, card_sdiff_of_subset (edgeFinset_mono hDle), card_edgeFinset_top_eq_card_choose_two,
      card_At hreg]
    have hprod : a * b = d ^ 2 / 4 := by
      rcases Nat.even_or_odd' d with ⟨t, rfl | rfl⟩
      · have ha : a = t := by rcases hbal v with h | h <;> omega
        have hb : b = t := by omega
        rw [ha, hb, show (2 * t) ^ 2 = 4 * (t * t) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
      · have h' : (a = t ∧ b = t + 1) ∨ (a = t + 1 ∧ b = t) := by rcases hbal v with h | h <;> omega
        rw [show (2 * t + 1) ^ 2 = 4 * (t * (t + 1)) + 1 by ring, Nat.mul_add_div (by norm_num)]
        rcases h' with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [ha, hb]; simp
        · rw [ha, hb, mul_comm]; simp
    omega
  calc S.card ≤ (univ.biUnion fun v => (Mv v).edgeFinset.image (ι v)).card := card_le_card hcover
    _ ≤ ∑ v, ((Mv v).edgeFinset.image (ι v)).card := card_biUnion_le
    _ ≤ ∑ v : V, (d.choose 2 - d ^ 2 / 4) := sum_le_sum fun v _ => card_image_le.trans (hcount v).le
    _ = _ := by rw [sum_const, card_univ, smul_eq_mul]

/-- **Sage result 2 (conditional equality).** With a balanced 2-edge-colouring, for every
triangle-free `H` with an edge, `|L(G), H| = n·⌊(d-1)²/4⌋`. -/
theorem line_eq {d : ℕ} (hreg : G.IsRegularOfDegree d) (c : G.edgeSet → Fin 2)
    (hbal : ∀ v, (univ.filter fun e : At G v => c e.1 = 0).card = d / 2 ∨
      (univ.filter fun e : At G v => c e.1 = 0).card = (d + 1) / 2)
    {H : SimpleGraph W} [DecidableEq W] (hH : H.CliqueFree 3) {u w : W} (huw : H.Adj u w) :
    nhf G.lineGraph H = ((Fintype.card V * ((d - 1) ^ 2 / 4) : ℕ) : ℕ∞) := by
  apply le_antisymm
  · have hK2 : (⊤ : SimpleGraph (Fin 2)) →g H :=
      ⟨![u, w], by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all [huw.symm]⟩
    rw [← choose_two_sub]
    exact (nhf_le_of_hom_target hK2).trans (line_upper hreg c hbal)
  · exact line_lower' hreg hH

/-- **Sage result 2, cubic case.** A cubic graph with a perfect matching (e.g. any bridgeless
cubic graph, by Petersen's theorem) has `|L(G), H| = n` for every triangle-free `H` with an edge. -/
theorem line_cubic_pm (hreg : G.IsRegularOfDegree 3) (M : G.Subgraph) (hM : M.IsPerfectMatching)
    {H : SimpleGraph W} [DecidableEq W] (hH : H.CliqueFree 3) {u w : W} (huw : H.Adj u w) :
    nhf G.lineGraph H = (Fintype.card V : ℕ∞) := by
  classical
  have h := line_eq hreg (fun e => if (e : Sym2 V) ∈ M.edgeSet then 0 else 1) ?_ hH huw
  · simpa using h
  · intro v
    left
    show _ = 1
    obtain ⟨x, hx, hxu⟩ := Subgraph.isPerfectMatching_iff.mp hM v
    rw [card_eq_one]
    refine ⟨⟨⟨s(v, x), M.adj_sub hx⟩, Sym2.mem_mk_left _ _⟩, ?_⟩
    ext ⟨⟨e, he⟩, hve⟩
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hmem
      split_ifs at hmem with hM'
      · obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hve
        have hy : M.Adj v y := hM'
        have hyx := hxu y hy
        subst hyx
        rfl
      · exact absurd hmem (by decide)
    · intro heq
      have he' : e = s(v, x) := congrArg (fun z : G.edgeSet => (z : Sym2 V)) (congrArg Subtype.val heq)
      subst he'
      rw [if_pos (show s(v, x) ∈ M.edgeSet from hx)]

end NonHom
