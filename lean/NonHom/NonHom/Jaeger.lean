import NonHom.Petersen

/-!
# Theorem 1 of `open_problems/README.md` (Jaeger / Petersen colourings)

**Theorem 1.** For every simple cubic graph `G`, `|L(G), L(P)| ≥ ℓ(G)`, where `ℓ(G)` is the number
of leaves of the bridge-block tree.

We prove the general form behind it: if `X₁, …, X_t` are pairwise disjoint vertex sets of a cubic
graph `G` and each `Xᵢ` is left by exactly one edge of `G`, then `|L(G), L(P)| ≥ t`. The vertex sets
of the leaf blocks form such a family (each is left only by its bridge), which gives Theorem 1.
The proof follows the README: P has six perfect matchings and every edge misses one of them; a
"good" vertex of `X` sends its three edges onto a star of `P`; a parity count then forces the
leaving edge into all six matchings.
-/

open SimpleGraph Finset

namespace NonHom

/-- The six perfect matchings of the Petersen graph. -/
def pm : Fin 6 → Finset (Sym2 (Fin 10)) :=
  ![{s(0, 1), s(2, 3), s(4, 9), s(5, 7), s(6, 8)},
    {s(0, 1), s(2, 7), s(3, 4), s(5, 8), s(6, 9)},
    {s(0, 4), s(1, 2), s(3, 8), s(5, 7), s(6, 9)},
    {s(0, 4), s(1, 6), s(2, 3), s(5, 8), s(7, 9)},
    {s(0, 5), s(1, 2), s(3, 4), s(6, 8), s(7, 9)},
    {s(0, 5), s(1, 6), s(2, 7), s(3, 8), s(4, 9)}]

/-- Every edge of `P` misses some perfect matching (in fact each edge lies in exactly two). -/
theorem pm_miss : ∀ e ∈ petersen.edgeFinset, ∃ j, e ∉ pm j := by decide +kernel

theorem pm_two : ∀ e ∈ petersen.edgeFinset, (univ.filter fun j => e ∈ pm j).card = 2 := by
  decide +kernel

/-- Three pairwise distinct, pairwise intersecting edges of `P` form a star (P is triangle-free),
so each perfect matching contains exactly one of them. -/
theorem pm_star : ∀ a ∈ petersen.edgeFinset, ∀ b ∈ petersen.edgeFinset, ∀ c ∈ petersen.edgeFinset,
    a ≠ b → a ≠ c → b ≠ c → (∃ w, w ∈ a ∧ w ∈ b) → (∃ w, w ∈ a ∧ w ∈ c) →
    (∃ w, w ∈ b ∧ w ∈ c) → ∀ j,
      (if a ∈ pm j then 1 else 0) + (if b ∈ pm j then 1 else 0) + (if c ∈ pm j then 1 else 0) = 1 := by
  decide +kernel

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Number of endpoints of `e` lying in `X`. -/
def cnt (X : Finset V) (e : Sym2 V) : ℕ := (X.filter (· ∈ e)).card

theorem cnt_le_two (X : Finset V) (e : Sym2 V) : cnt X e ≤ 2 := by
  induction e using Sym2.ind with
  | _ u v =>
    unfold cnt
    calc _ ≤ ({u, v} : Finset V).card := card_le_card (fun x hx => by
          simp only [mem_filter, Sym2.mem_iff] at hx; simp [hx.2])
      _ ≤ 2 := card_le_two

theorem sum_incident (F : Finset (Sym2 V)) (X : Finset V) :
    ∑ x ∈ X, (F.filter (x ∈ ·)).card = ∑ e ∈ F, cnt X e := by
  simp only [cnt, card_filter]
  exact sum_comm

theorem sum_cnt_mod_two (F : Finset (Sym2 V)) (X : Finset V) :
    (∑ e ∈ F, cnt X e) % 2 = (F.filter (cnt X · = 1)).card % 2 := by
  have : ∀ e ∈ F, cnt X e = (if cnt X e = 1 then 1 else 0) + 2 * (if cnt X e = 2 then 1 else 0) := by
    intro e _; have := cnt_le_two X e; split_ifs <;> omega
  rw [sum_congr rfl this, sum_add_distrib, ← mul_sum, ← card_filter]
  omega

section phi

variable (S : Finset (Sym2 G.edgeSet)) (φ : G.lineGraph.deleteEdges ↑S →g petersen.lineGraph)

/-- `φ` read on edges of `G`. -/
noncomputable def phiE (e : Sym2 V) : Sym2 (Fin 10) :=
  if h : e ∈ G.edgeSet then (φ ⟨e, h⟩).val else s(0, 0)

/-- `x` is good if none of the line-graph edges between edges at `x` was deleted. -/
def Good (x : V) : Prop :=
  ∀ e f : G.edgeSet, e ≠ f → x ∈ (e : Sym2 V) → x ∈ (f : Sym2 V) → s(e, f) ∉ S

theorem phiE_mem (e : Sym2 V) (he : e ∈ G.edgeSet) : phiE S φ e ∈ petersen.edgeFinset := by
  rw [phiE, dif_pos he, mem_edgeFinset]; exact (φ ⟨e, he⟩).property

theorem good_adj {x : V} (hx : Good S x) {e f : Sym2 V} (he : e ∈ G.edgeSet) (hf : f ∈ G.edgeSet)
    (hef : e ≠ f) (hxe : x ∈ e) (hxf : x ∈ f) :
    phiE S φ e ≠ phiE S φ f ∧ ∃ w, w ∈ phiE S φ e ∧ w ∈ phiE S φ f := by
  have hne : (⟨e, he⟩ : G.edgeSet) ≠ ⟨f, hf⟩ := fun h => hef (congrArg Subtype.val h)
  have hadj : (G.lineGraph.deleteEdges ↑S).Adj ⟨e, he⟩ ⟨f, hf⟩ := by
    rw [deleteEdges_adj, lineGraph_adj_iff_exists]
    exact ⟨⟨hne, x, hxe, hxf⟩, hx _ _ hne hxe hxf⟩
  have h := φ.map_rel hadj
  rw [lineGraph_adj_iff_exists] at h
  obtain ⟨hne', w, hw1, hw2⟩ := h
  rw [phiE, phiE, dif_pos he, dif_pos hf]
  exact ⟨fun h' => hne' (Subtype.ext h'), w, hw1, hw2⟩

/-- A good vertex of a cubic graph has exactly one incident edge mapped into each matching. -/
theorem good_count (hcub : G.IsRegularOfDegree 3) {x : V} (hx : Good S x) (j : Fin 6) :
    (G.edgeFinset.filter fun e => x ∈ e ∧ phiE S φ e ∈ pm j).card = 1 := by
  have h3 : (G.incidenceFinset x).card = 3 := by
    rw [card_incidenceFinset_eq_degree, hcub.degree_eq]
  obtain ⟨a, b, c, hab, hac, hbc, habc⟩ := card_eq_three.mp h3
  have mem : ∀ e, e ∈ G.incidenceFinset x ↔ e ∈ G.edgeSet ∧ x ∈ e := fun e => by
    rw [mem_incidenceFinset]; rfl
  have ha := (mem a).mp (by rw [habc]; simp)
  have hb := (mem b).mp (by rw [habc]; simp)
  have hc := (mem c).mp (by rw [habc]; simp)
  have hfilt : (G.edgeFinset.filter fun e => x ∈ e ∧ phiE S φ e ∈ pm j) =
      ({a, b, c} : Finset (Sym2 V)).filter (fun e => phiE S φ e ∈ pm j) := by
    ext e
    simp only [mem_filter, mem_edgeFinset]
    rw [← habc, mem]
    tauto
  rw [hfilt, card_filter, sum_insert (by simp [hab, hac]), sum_insert (by simp [hbc]), sum_singleton,
    ← add_assoc]
  have hab' := good_adj S φ hx ha.1 hb.1 hab ha.2 hb.2
  have hac' := good_adj S φ hx ha.1 hc.1 hac ha.2 hc.2
  have hbc' := good_adj S φ hx hb.1 hc.1 hbc hb.2 hc.2
  exact pm_star _ (phiE_mem S φ a ha.1) _ (phiE_mem S φ b hb.1) _ (phiE_mem S φ c hc.1)
    hab'.1 hac'.1 hbc'.1 hab'.2 hac'.2 hbc'.2 j

include φ in
/-- **Key lemma.** If `X` is left by exactly one edge `b`, then `X` contains a bad vertex. -/
theorem exists_bad (hcub : G.IsRegularOfDegree 3) (X : Finset V) (b : Sym2 V)
    (hb : b ∈ G.edgeSet) (hbX : cnt X b = 1) (huniq : ∀ e ∈ G.edgeSet, cnt X e = 1 → e = b) :
    ∃ x ∈ X, ¬ Good S x := by
  by_contra hcon
  push Not at hcon
  have crossing : ∀ F ⊆ G.edgeFinset, (F.filter (cnt X · = 1)).card = if b ∈ F then 1 else 0 := by
    intro F hF
    split_ifs with hbF
    · rw [card_eq_one]; refine ⟨b, ?_⟩
      ext e; simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨he, h1⟩; exact huniq e (mem_edgeFinset.mp (hF he)) h1
      · rintro rfl; exact ⟨hbF, hbX⟩
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro e he h1
      exact hbF (huniq e (mem_edgeFinset.mp (hF he)) h1 ▸ he)
  -- |X| is odd
  have hodd : X.card % 2 = 1 := by
    have h := sum_cnt_mod_two G.edgeFinset X
    rw [← sum_incident, crossing _ subset_rfl, if_pos (mem_edgeFinset.mpr hb)] at h
    have : ∀ x ∈ X, (G.edgeFinset.filter (x ∈ ·)).card = 3 := by
      intro x _
      rw [← incidenceFinset_eq_filter, card_incidenceFinset_eq_degree, hcub.degree_eq]
    rw [sum_congr rfl this, sum_const, smul_eq_mul] at h
    omega
  -- the leaving edge lies in every perfect matching
  have hall : ∀ j, phiE S φ b ∈ pm j := by
    intro j
    let A := G.edgeFinset.filter fun e => phiE S φ e ∈ pm j
    have h := sum_cnt_mod_two A X
    rw [← sum_incident, crossing A (filter_subset _ _)] at h
    have : ∀ x ∈ X, (A.filter (x ∈ ·)).card = 1 := by
      intro x hx
      rw [← good_count S φ hcub (hcon x hx) j, filter_filter]
      congr 1; ext e; simp [and_comm]
    rw [sum_congr rfl this, sum_const, smul_eq_mul, mul_one, hodd] at h
    by_contra hnot
    have : b ∉ A := fun h' => hnot (mem_filter.mp h').2
    rw [if_neg this] at h
    omega
  obtain ⟨j, hj⟩ := pm_miss _ (phiE_mem S φ b hb)
  exact hj (hall j)

end phi

/-- **Theorem 1** (general form). If `X₁, …, X_t` are pairwise disjoint vertex sets of a cubic
graph, each left by exactly one edge, then `|L(G), L(P)| ≥ t`. -/
theorem jaeger_lower (hcub : G.IsRegularOfDegree 3) (t : ℕ) (X : Fin t → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (X i) (X j)) (b : Fin t → Sym2 V)
    (hb : ∀ i, b i ∈ G.edgeSet) (hbX : ∀ i, cnt (X i) (b i) = 1)
    (huniq : ∀ i, ∀ e ∈ G.edgeSet, cnt (X i) e = 1 → e = b i) :
    (t : ℕ∞) ≤ nhf G.lineGraph petersen.lineGraph := by
  apply le_nhf
  intro S ⟨φ⟩
  have hbad := fun i => exists_bad S φ hcub (X i) (b i) (hb i) (hbX i) (huniq i)
  choose x hxX hxbad using hbad
  have hpair : ∀ i, ∃ e f : G.edgeSet, e ≠ f ∧ x i ∈ (e : Sym2 V) ∧ x i ∈ (f : Sym2 V) ∧ s(e, f) ∈ S := by
    intro i
    have := hxbad i
    simp only [Good, not_forall, not_not] at this
    obtain ⟨e, f, hef, h1, h2, h3⟩ := this
    exact ⟨e, f, hef, h1, h2, h3⟩
  choose e f hef hxe hxf hS using hpair
  have hinj : Set.InjOn (fun i => s(e i, f i)) (univ : Finset (Fin t)) := by
    intro i _ j _ hij
    simp only at hij
    by_contra hne
    have hxx : x i ≠ x j := by
      intro h
      exact Finset.disjoint_left.mp (hdisj i j hne) (hxX i) (h ▸ hxX j)
    -- both `x i` and `x j` lie on `e i` and on `f i`
    have hj : (x j ∈ (e i : Sym2 V)) ∧ (x j ∈ (f i : Sym2 V)) := by
      rcases Sym2.eq_iff.mp hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by rw [h1]; exact hxe j, by rw [h2]; exact hxf j⟩
      · exact ⟨by rw [h1]; exact hxf j, by rw [h2]; exact hxe j⟩
    have h1 := (Sym2.mem_and_mem_iff hxx).mp ⟨hxe i, hj.1⟩
    have h2 := (Sym2.mem_and_mem_iff hxx).mp ⟨hxf i, hj.2⟩
    exact hef i (Subtype.ext (h1.trans h2.symm))
  have := card_le_card_of_injOn (fun i => s(e i, f i)) (fun i _ => hS i) hinj
  rw [card_univ, Fintype.card_fin] at this
  exact_mod_cast this

end NonHom
