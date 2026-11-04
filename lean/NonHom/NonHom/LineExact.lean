import NonHom.Generalize
import NonHom.Triangular

/-!
# Line graphs: exactness for every target from a proper edge colouring

**Theorem.** Let `G` be `d`-regular on `n` vertices with a proper `d`-edge-colouring (for example
any bipartite regular graph, by König's theorem — cited, not formalized). Let `H` contain `K_r`
and be `K_{r+1}`-free (`r ≥ 1`). Then `|L(G), H| = n·(C(d,2) - t(d,r))`.

Grouping the `d` edge colours by residue mod `r` makes every vertex star a relabelled Turán graph.
This gives exact ground-state energies for kagome = L(honeycomb), pyrochlore = L(diamond),
checkerboard = L(square) on bipartite tori, for every target with clique number `r`.
-/

open SimpleGraph Finset

namespace NonHom

variable {V W : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Upper bound from any `r`-colouring of the edges of `G`. -/
theorem line_upper_r {d r : ℕ} (c : G.edgeSet → Fin r) :
    nhf G.lineGraph (⊤ : SimpleGraph (Fin r)) ≤
      ((∑ v, ((⊤ : SimpleGraph (At G v)) \
        (⊤ : SimpleGraph (Fin r)).comap (fun e => c e.1)).edgeFinset.card : ℕ) : ℕ∞) := by
  classical
  let Mono : SimpleGraph G.edgeSet := G.lineGraph ⊓ SimpleGraph.fromRel fun a b => c a = c b
  let S : Finset (Sym2 G.edgeSet) := Mono.edgeFinset
  have hhom : Nonempty (G.lineGraph.deleteEdges ↑S →g (⊤ : SimpleGraph (Fin r))) := by
    refine ⟨⟨c, fun {a b} h => ?_⟩⟩
    rw [deleteEdges_adj] at h
    intro hab
    apply h.2
    simp only [S, coe_edgeFinset]
    exact ⟨h.1, h.1.ne, Or.inl hab⟩
  refine (nhf_le_card S hhom).trans ?_
  norm_cast
  let Mv : ∀ v, SimpleGraph (At G v) := fun v =>
    (⊤ : SimpleGraph (At G v)) \ (⊤ : SimpleGraph (Fin r)).comap (fun e => c e.1)
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
  calc S.card ≤ (univ.biUnion fun v => (Mv v).edgeFinset.image (ι v)).card := card_le_card hcover
    _ ≤ ∑ v, ((Mv v).edgeFinset.image (ι v)).card := card_biUnion_le
    _ ≤ ∑ v, (Mv v).edgeFinset.card := sum_le_sum fun v _ => card_image_le
    _ = _ := by
        apply sum_congr rfl; intro v _
        apply Finset.card_bij (fun z _ => z) (fun z hz => by convert hz using 1)
          (fun _ _ _ _ h => h) (fun z hz => ⟨z, by convert hz using 1, rfl⟩)

/-- **Exactness theorem.** -/
theorem nhf_line_class1 {d r : ℕ} (hreg : G.IsRegularOfDegree d) (hr : 0 < r)
    (κ : G.edgeSet → Fin d)
    (hκ : ∀ v : V, ∀ e f : At G v, κ e.1 = κ f.1 → e = f)
    {H : SimpleGraph W} [DecidableEq W] (hcf : H.CliqueFree (r + 1))
    (hK : (⊤ : SimpleGraph (Fin r)) →g H) :
    nhf G.lineGraph H = ((Fintype.card V * (d.choose 2 - turanNumber d r) : ℕ) : ℕ∞) := by
  classical
  apply le_antisymm _ (line_lower_clique hreg hcf)
  refine (nhf_le_of_hom_target hK).trans ?_
  let c : G.edgeSet → Fin r := fun e => ⟨(κ e).val % r, Nat.mod_lt _ hr⟩
  refine (line_upper_r (d := d) c).trans ?_
  norm_cast
  have hσ : ∀ v : V, ∃ σ : At G v ≃ Fin d, ∀ e, σ e = κ e.1 := by
    intro v
    have hinj : Function.Injective (fun e : At G v => κ e.1) := fun e f h => hκ v e f h
    have hcard : Fintype.card (At G v) = Fintype.card (Fin d) := by
      rw [card_At hreg, Fintype.card_fin]
    exact ⟨Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩),
      fun e => rfl⟩
  have hcount : ∀ v : V, ((⊤ : SimpleGraph (At G v)) \
      (⊤ : SimpleGraph (Fin r)).comap (fun e => c e.1)).edgeFinset.card = d.choose 2 - turanNumber d r := by
    intro v
    obtain ⟨σ, hσe⟩ := hσ v
    have hcomap : (⊤ : SimpleGraph (Fin r)).comap (fun e : At G v => c e.1) = (turanGraph d r).comap σ := by
      ext a b
      simp only [comap_adj, top_adj, turanGraph_adj, hσe, c, ne_eq, Fin.mk.injEq]
    have hsd : ((⊤ : SimpleGraph (At G v)) \ (⊤ : SimpleGraph (Fin r)).comap (fun e => c e.1)).edgeFinset =
        (⊤ : SimpleGraph (At G v)).edgeFinset \
          ((⊤ : SimpleGraph (Fin r)).comap (fun e : At G v => c e.1)).edgeFinset := by
      ext z
      rw [mem_edgeFinset, mem_sdiff, mem_edgeFinset, mem_edgeFinset]
      simp only [edgeSet_sdiff, Set.mem_diff]
    rw [hsd, card_sdiff_of_subset (edgeFinset_mono le_top), card_edgeFinset_top_eq_card_choose_two,
      card_At hreg]
    congr 1
    have e := (SimpleGraph.Iso.comap σ (turanGraph d r)).card_edgeFinset_eq
    rw [turanNumber, ← e, edgeFinset_card, edgeFinset_card]
    exact Fintype.card_congr' (by rw [hcomap])
  rw [sum_congr rfl (fun v _ => hcount v), sum_const, card_univ, smul_eq_mul]

end NonHom
