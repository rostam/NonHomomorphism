import NonHom.Generalize

/-!
# Hamming graphs

The Hamming graph `H(d,n) = K_n □ ⋯ □ K_n` (`d` factors) has vertex set `[n]^d`, two words
adjacent iff they differ in exactly one coordinate. It contains `K_n` (`d = 1`), rook's graphs
(`d = 2`) and hypercubes (`n = 2`).

**Theorem.** If `H` contains `K_r` and is `K_{r+1}`-free (`r ≥ 1`), then
`|H(d,n), H| = d·n^{d-1}·(C(n,2) - t(n,r))`.

The edges split into `d·n^{d-1}` lines, each a copy of `K_n`; each line must lose
`C(n,2) - t(n,r)` edges (Turán), and the colouring `x ↦ (∑ xᵢ mod n) mod r` loses exactly that
many on every line.
-/

open SimpleGraph Finset

namespace NonHom

variable {W : Type*} (d n : ℕ)

/-- The Hamming graph `H(d,n)`. -/
def ham : SimpleGraph (Fin d → Fin n) where
  Adj x y := (univ.filter fun i => x i ≠ y i).card = 1
  symm := ⟨fun x y h => by simpa [ne_comm] using h⟩
  loopless := ⟨fun x h => by simp at h⟩

instance : DecidableRel (ham d n).Adj := fun x y =>
  inferInstanceAs (Decidable ((univ.filter fun i => x i ≠ y i).card = 1))

variable {d n}

/-- The line through `z` in direction `i`. -/
def lineMap (i : Fin d) (z : Fin d → Fin n) (a : Fin n) : Fin d → Fin n := Function.update z i a

theorem lineMap_injective (i : Fin d) (z : Fin d → Fin n) : Function.Injective (lineMap i z) := by
  intro a b h
  have := congrFun h i
  simpa [lineMap] using this

theorem lineMap_adj (i : Fin d) (z : Fin d → Fin n) {a b : Fin n} (hab : a ≠ b) :
    (ham d n).Adj (lineMap i z a) (lineMap i z b) := by
  show (univ.filter fun j => lineMap i z a j ≠ lineMap i z b j).card = 1
  rw [card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  rw [mem_filter, mem_singleton]
  by_cases hj : j = i
  · subst hj; simp [lineMap, hab]
  · simp [lineMap, Function.update_of_ne hj, hj]

/-- Every edge lies on a line: `x`, `y` differ exactly at `i`, and `y = update x i (y i)`. -/
theorem ham_adj_line {x y : Fin d → Fin n} (h : (ham d n).Adj x y) :
    ∃ i, x i ≠ y i ∧ y = Function.update x i (y i) := by
  obtain ⟨i, hi⟩ := card_eq_one.mp h
  refine ⟨i, ?_, funext fun j => ?_⟩
  · have := (Finset.ext_iff.mp hi i).mpr (mem_singleton_self i)
    simpa using this
  · by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj]
      by_contra hne
      have := (Finset.ext_iff.mp hi j).mp (by simpa [eq_comm] using hne)
      exact hj (mem_singleton.mp this)

/-- Lines: a direction `i` and a base point with `z i = 0`. -/
abbrev Lines (d n : ℕ) [NeZero n] := {p : Fin d × (Fin d → Fin n) // p.2 p.1 = 0}

theorem card_fiber [NeZero n] (i : Fin d) :
    Fintype.card {z : Fin d → Fin n // z i = 0} = n ^ (d - 1) := by
  classical
  rw [Fintype.card_congr ((Equiv.piSplitAt i (fun _ => Fin n)).subtypeEquiv
    (p := fun z => z i = 0) (q := fun p => p.1 = 0) (fun z => Iff.rfl))]
  rw [Fintype.card_subtype]
  rw [show (univ.filter fun x : Fin n × ({j // j ≠ i} → Fin n) => x.1 = 0) = {0} ×ˢ univ by
    ext ⟨a, w⟩; simp [eq_comm]]
  simp

theorem card_Lines [NeZero n] : Fintype.card (Lines d n) = d * n ^ (d - 1) := by
  classical
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun i (z : Fin d → Fin n) => z i = 0)),
    Fintype.card_sigma]
  simp only [card_fiber, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

variable {H : SimpleGraph W} [DecidableEq W]

/-- **Lower bound.** -/
theorem ham_lower [NeZero n] {r : ℕ} (hH : H.CliqueFree (r + 1)) :
    ((d * n ^ (d - 1) * (n.choose 2 - turanNumber n r) : ℕ) : ℕ∞) ≤ nhf (ham d n) H := by
  classical
  apply le_nhf
  intro S ⟨g⟩
  set K := (ham d n).deleteEdges ↑S
  have hK : K.CliqueFree (r + 1) := cliqueFree_of_hom g hH
  let Kl : Lines d n → SimpleGraph (Fin n) := fun l => K.comap (lineMap l.1.1 l.1.2)
  have hKl : ∀ l, (Kl l).CliqueFree (r + 1) := fun l =>
    cliqueFree_of_hom (⟨lineMap l.1.1 l.1.2, fun h => h⟩ : Kl l →g K) hK
  let D : Lines d n → Finset (Sym2 (Fin n)) := fun l =>
    (⊤ : SimpleGraph (Fin n)).edgeFinset \ (Kl l).edgeFinset
  have hD : ∀ l, n.choose 2 - turanNumber n r ≤ (D l).card := by
    intro l
    have h1 := (hKl l).card_edgeFinset_le
    rw [Fintype.card_fin] at h1
    have h1' : (Kl l).edgeFinset.card ≤ turanNumber n r := by convert h1
    have h2 : (D l).card = (⊤ : SimpleGraph (Fin n)).edgeFinset.card - (Kl l).edgeFinset.card :=
      card_sdiff_of_subset (edgeFinset_mono le_top)
    rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin] at h2
    omega
  let ι : Lines d n → Sym2 (Fin n) → Sym2 (Fin d → Fin n) := fun l => Sym2.map (lineMap l.1.1 l.1.2)
  have hsub : ∀ l, (D l).image (ι l) ⊆ S := by
    intro l z hz
    obtain ⟨z, hzD, rfl⟩ := mem_image.mp hz
    simp only [D, mem_sdiff, mem_edgeFinset] at hzD
    obtain ⟨htop, hnot⟩ := hzD
    induction z using Sym2.ind with
    | _ a b =>
      have hab : a ≠ b := htop
      by_contra hS
      apply hnot
      show K.Adj (lineMap l.1.1 l.1.2 a) (lineMap l.1.1 l.1.2 b)
      rw [deleteEdges_adj]
      exact ⟨lineMap_adj _ _ hab, hS⟩
  have hdisj : ∀ l ∈ (univ : Finset (Lines d n)), ∀ l' ∈ (univ : Finset (Lines d n)), l ≠ l' →
      Disjoint ((D l).image (ι l)) ((D l').image (ι l')) := by
    intro l _ l' _ hll'
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨z, hz, rfl⟩ := mem_image.mp he
    obtain ⟨z', -, hz'⟩ := mem_image.mp he'
    simp only [D, mem_sdiff, mem_edgeFinset] at hz
    induction z using Sym2.ind with
    | _ a b =>
      induction z' using Sym2.ind with
      | _ a' b' =>
        apply hll'
        have hab : a ≠ b := hz.1
        obtain ⟨⟨i, y⟩, hy⟩ := l
        obtain ⟨⟨i', y'⟩, hy'⟩ := l'
        simp only [ι, Sym2.map_mk, Sym2.eq_iff] at hz'
        -- the two endpoints lie on both lines
        have both : ∀ c c' : Fin n, (lineMap i' y' c = lineMap i y a ∧ lineMap i' y' c' = lineMap i y b) →
            (⟨(i, y), hy⟩ : Lines d n) = ⟨(i', y'), hy'⟩ := by
          rintro c c' ⟨h1, h2⟩
          have hii : i = i' := by
            by_contra hne
            have e1 := congrFun h1 i
            have e2 := congrFun h2 i
            simp only [lineMap, Function.update_of_ne hne, Function.update_self] at e1 e2
            exact hab (e1.symm.trans e2)
          subst hii
          have hyy : y = y' := by
            funext j
            by_cases hj : j = i
            · subst hj; exact (show y j = 0 from hy).trans (show y' j = 0 from hy').symm
            · have := congrFun h1 j
              simp only [lineMap, Function.update_of_ne hj] at this
              exact this.symm
          subst hyy; rfl
        rcases hz' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact both a' b' ⟨h1, h2⟩
        · exact both b' a' ⟨h2, h1⟩
  have hbig : (univ.biUnion fun l => (D l).image (ι l)) ⊆ S := biUnion_subset.mpr fun l _ => hsub l
  have hcard := card_le_card hbig
  rw [card_biUnion hdisj] at hcard
  have : ∑ _l : Lines d n, (n.choose 2 - turanNumber n r) ≤ ∑ l : Lines d n, ((D l).image (ι l)).card := by
    apply sum_le_sum; intro l _
    rw [card_image_of_injective _ (Sym2.map.injective (lineMap_injective _ _))]; exact hD l
  rw [sum_const, card_univ, card_Lines, smul_eq_mul] at this
  exact_mod_cast this.trans hcard

/-- The Latin colouring `x ↦ (∑ xᵢ mod n) mod r`. -/
def latin (r : ℕ) (hr : 0 < r) (x : Fin d → Fin n) : Fin r :=
  ⟨((∑ j, (x j).val) % n) % r, Nat.mod_lt _ hr⟩

theorem sum_lineMap [NeZero n] (i : Fin d) (z : Fin d → Fin n) (hz : z i = 0) (a : Fin n) :
    ∑ j, (lineMap i z a j).val = (∑ j, (z j).val) + a.val := by
  have h1 := Finset.sum_update_of_mem (mem_univ i) (fun j => (z j).val) a.val
  have e : (fun j => (lineMap i z a j).val) = Function.update (fun j => (z j).val) i a.val := by
    funext j; by_cases hj : j = i
    · subst hj; simp [lineMap]
    · simp [lineMap, Function.update_of_ne hj]
  rw [e, h1, ← Finset.add_sum_erase _ _ (mem_univ i), hz]
  rw [show (univ \ {i} : Finset (Fin d)) = univ.erase i by ext; simp]
  simp [add_comm]

/-- On each line the Latin colouring is a relabelled Turán graph. -/
theorem latin_line_iso [NeZero n] (r : ℕ) (hr : 0 < r) (i : Fin d) (z : Fin d → Fin n) (hz : z i = 0) :
    ∃ σ : Fin n ≃ Fin n, (⊤ : SimpleGraph (Fin r)).comap (latin r hr ∘ lineMap i z) =
      (turanGraph n r).comap σ := by
  refine ⟨Equiv.addLeft (⟨(∑ j, (z j).val) % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩ : Fin n), ?_⟩
  ext a b
  simp only [comap_adj, top_adj, Function.comp_apply, turanGraph_adj, Equiv.coe_addLeft, latin,
    ne_eq, Fin.mk.injEq, sum_lineMap i z hz, Fin.val_add, Nat.mod_add_mod]

/-- **Upper bound.** -/
theorem ham_upper [NeZero n] {r : ℕ} (hr : 0 < r) (hK : (⊤ : SimpleGraph (Fin r)) →g H) :
    nhf (ham d n) H ≤ ((d * n ^ (d - 1) * (n.choose 2 - turanNumber n r) : ℕ) : ℕ∞) := by
  classical
  let c := latin (d := d) (n := n) r hr
  let Mono : SimpleGraph (Fin d → Fin n) := ham d n ⊓ SimpleGraph.fromRel fun x y => c x = c y
  let S : Finset (Sym2 (Fin d → Fin n)) := Mono.edgeFinset
  have hhom : Nonempty ((ham d n).deleteEdges ↑S →g H) := by
    refine ⟨hK.comp ⟨c, fun {x y} h => ?_⟩⟩
    rw [deleteEdges_adj] at h
    intro hxy
    apply h.2
    simp only [S, coe_edgeFinset]
    exact ⟨h.1, h.1.ne, Or.inl hxy⟩
  refine (nhf_le_card S hhom).trans ?_
  norm_cast
  -- monochromatic pairs on a line
  let Ml : Lines d n → SimpleGraph (Fin n) := fun l =>
    (⊤ : SimpleGraph (Fin n)) \ (⊤ : SimpleGraph (Fin r)).comap (c ∘ lineMap l.1.1 l.1.2)
  let ι : Lines d n → Sym2 (Fin n) → Sym2 (Fin d → Fin n) := fun l => Sym2.map (lineMap l.1.1 l.1.2)
  have hcover : S ⊆ univ.biUnion fun l => (Ml l).edgeFinset.image (ι l) := by
    intro e he
    simp only [S, mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨hadj, -, hcol⟩ := he
      simp only at hadj hcol
      have hcxy : c x = c y := hcol.elim id Eq.symm
      obtain ⟨i, hne, hy⟩ := ham_adj_line hadj
      let z := Function.update x i 0
      have hz : z i = 0 := by simp [z]
      have hx' : lineMap i z (x i) = x := by simp [lineMap, z]
      have hy' : lineMap i z (y i) = y := by
        have e : lineMap i z (y i) = Function.update x i (y i) := by simp [lineMap, z]
        rw [e]; exact hy.symm
      rw [mem_biUnion]
      refine ⟨⟨(i, z), hz⟩, mem_univ _, mem_image.mpr ⟨s(x i, y i), ?_, ?_⟩⟩
      · rw [mem_edgeFinset]
        show (Ml ⟨(i, z), hz⟩).Adj (x i) (y i)
        refine ⟨hne, fun h => h ?_⟩
        show c (lineMap i z (x i)) = c (lineMap i z (y i))
        rw [hx', hy']; exact hcxy
      · simp only [ι, Sym2.map_mk, hx', hy']
  have hcount : ∀ l, (Ml l).edgeFinset.card = n.choose 2 - turanNumber n r := by
    intro l
    obtain ⟨σ, hσ⟩ := latin_line_iso r hr l.1.1 l.1.2 l.2
    have hsd : (Ml l).edgeFinset = (⊤ : SimpleGraph (Fin n)).edgeFinset \
        ((⊤ : SimpleGraph (Fin r)).comap (c ∘ lineMap l.1.1 l.1.2)).edgeFinset := by
      ext e; simp [Ml, edgeSet_sdiff]
    rw [hsd, card_sdiff_of_subset (edgeFinset_mono le_top), card_edgeFinset_top_eq_card_choose_two,
      Fintype.card_fin]
    have : ((⊤ : SimpleGraph (Fin r)).comap (c ∘ lineMap l.1.1 l.1.2)).edgeFinset.card =
        turanNumber n r := by
      have e := (SimpleGraph.Iso.comap σ (turanGraph n r)).card_edgeFinset_eq
      rw [turanNumber, ← e, edgeFinset_card, edgeFinset_card]
      exact Fintype.card_congr' (by simp only [c]; rw [hσ])
    rw [this]
  calc S.card ≤ (univ.biUnion fun l => (Ml l).edgeFinset.image (ι l)).card := card_le_card hcover
    _ ≤ ∑ l, ((Ml l).edgeFinset.image (ι l)).card := card_biUnion_le
    _ ≤ ∑ _l : Lines d n, (n.choose 2 - turanNumber n r) :=
        sum_le_sum fun l _ => card_image_le.trans (hcount l).le
    _ = _ := by rw [sum_const, card_univ, card_Lines, smul_eq_mul]

/-- **Hamming-graph theorem.** If `H` contains `K_r` and is `K_{r+1}`-free (`r ≥ 1`), then
`|H(d,n), H| = d·n^{d-1}·(C(n,2) - t(n,r))`. -/
theorem nhf_ham [NeZero n] {r : ℕ} (hr : 0 < r) (hcf : H.CliqueFree (r + 1))
    (hK : (⊤ : SimpleGraph (Fin r)) →g H) :
    nhf (ham d n) H = ((d * n ^ (d - 1) * (n.choose 2 - turanNumber n r) : ℕ) : ℕ∞) :=
  le_antisymm (ham_upper hr hK) (ham_lower hcf)

end NonHom
