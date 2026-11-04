import NonHom.LineGraph

/-!
# Generalizations

* `nhf_top_clique`: `|K_n,H| = C(n,2) - t(n,r)` whenever `K_r → H` and `H` is `K_{r+1}`-free,
  i.e. `|K_n,H|` depends only on the clique number of `H`.
* `line_lower_clique`: `|L(G),H| ≥ n·(C(d,2) - t(d,r))` for `d`-regular `G` and `K_{r+1}`-free `H`.
* `nhf_edge_transitive`: if `G` is edge-transitive and `F → G` but `F ↛ H`, then
  `|E(G)| ≤ |E(F)|·|G,H|`.
-/

open SimpleGraph Finset

namespace NonHom

variable {V W U : Type*}

/-! ### Complete graphs: only the clique number matters -/

/-- **Clique-number theorem.** If `H` contains `K_r` and is `K_{r+1}`-free (`r ≥ 1`), then
`|K_n,H| = C(n,2) - t(n,r)`. -/
theorem nhf_top_clique (n r : ℕ) (hr : 0 < r) {H : SimpleGraph W} [DecidableEq W]
    (hcf : H.CliqueFree (r + 1)) (hK : (⊤ : SimpleGraph (Fin r)) →g H) :
    nhf (⊤ : SimpleGraph (Fin n)) H = ((n.choose 2 - turanNumber n r : ℕ) : ℕ∞) := by
  apply le_antisymm
  · rw [← nhf_top_top n r hr]; exact nhf_le_of_hom_target hK
  · apply le_nhf
    intro S ⟨f⟩
    have hle := (cliqueFree_of_hom f hcf).card_edgeFinset_le
    rw [Fintype.card_fin] at hle
    have hE : ((⊤ : SimpleGraph (Fin n)).deleteEdges ↑S).edgeFinset =
        (⊤ : SimpleGraph (Fin n)).edgeFinset \ S := edgeFinset_deleteEdges S
    rw [hE] at hle
    have := card_le_card_sdiff_add_card (s := (⊤ : SimpleGraph (Fin n)).edgeFinset) (t := S)
    rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin] at this
    norm_cast
    omega

/-! ### Line graphs and general clique number -/

section line

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem line_lower_clique {d r : ℕ} (hreg : G.IsRegularOfDegree d) {H : SimpleGraph W} [DecidableEq W]
    (hH : H.CliqueFree (r + 1)) :
    ((Fintype.card V * (d.choose 2 - turanNumber d r) : ℕ) : ℕ∞) ≤ nhf G.lineGraph H := by
  classical
  apply le_nhf
  intro S ⟨g⟩
  set K := G.lineGraph.deleteEdges ↑S
  have hK : K.CliqueFree (r + 1) := cliqueFree_of_hom g hH
  -- the kept part of each clique
  let Kv : ∀ v, SimpleGraph (At G v) := fun v => K.comap (fun e => e.1)
  have hKv : ∀ v, (Kv v).CliqueFree (r + 1) := fun v =>
    cliqueFree_of_hom (⟨fun e => e.1, fun h => h⟩ : Kv v →g K) hK
  let D : ∀ v, Finset (Sym2 (At G v)) := fun v =>
    (⊤ : SimpleGraph (At G v)).edgeFinset \ (Kv v).edgeFinset
  have hD : ∀ v, d.choose 2 - turanNumber d r ≤ (D v).card := by
    intro v
    have h1 := (hKv v).card_edgeFinset_le
    rw [card_At hreg] at h1
    have h1' : (Kv v).edgeFinset.card ≤ turanNumber d r := by convert h1
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
  have : ∑ v : V, (d.choose 2 - turanNumber d r) ≤ ∑ v : V, ((D v).image (ι v)).card := by
    apply sum_le_sum; intro v _
    rw [card_image_of_injective _ (hιinj v)]; exact hD v
  rw [sum_const, card_univ, smul_eq_mul] at this
  exact_mod_cast this.trans hcard

end line

/-! ### Edge-transitive graphs -/

section transitive

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  [Fintype U] {F : SimpleGraph U} [DecidableRel F.Adj] {H : SimpleGraph W}

/-- An automorphism as a homomorphism. -/
def autHom (σ : G ≃g G) : G →g G := σ.toEmbedding.toHom

theorem autHom_injective (σ : G ≃g G) : Function.Injective (autHom σ) := σ.injective

/-- The automorphism group is finite. -/
noncomputable instance : Fintype (G ≃g G) := by
  classical
  exact Fintype.ofInjective (fun σ : G ≃g G => (σ.toEquiv : V ≃ V)) RelIso.toEquiv_injective

/-- `c e = ∑_σ μ(σ∘φ, e)`: the total load of `e` over all automorphic images of `φ`. -/
noncomputable def totLoad (φ : F →g G) (e : Sym2 V) : ℕ := ∑ σ : G ≃g G, load ((autHom σ).comp φ) e

theorem totLoad_transfer (φ : F →g G) (τ : G ≃g G) (e : Sym2 V) :
    totLoad φ (e.map τ) = totLoad φ e := by
  unfold totLoad
  let eqv : (G ≃g G) ≃ (G ≃g G) :=
    { toFun := fun σ => σ.trans τ.symm
      invFun := fun σ => σ.trans τ
      left_inv := fun σ => by ext x; simp
      right_inv := fun σ => by ext x; simp }
  calc ∑ σ : G ≃g G, load ((autHom σ).comp φ) (e.map τ)
      = ∑ σ : G ≃g G, load ((autHom (σ.trans τ.symm)).comp φ) e := sum_congr rfl (fun σ _ => ?_)
    _ = ∑ σ : G ≃g G, load ((autHom σ).comp φ) e := Fintype.sum_equiv eqv _ _ (fun _ => rfl)
  have h := load_comp_injective ((autHom (σ.trans τ.symm)).comp φ) (autHom τ) (autHom_injective τ) e
  have hcomp : (autHom τ).comp ((autHom (σ.trans τ.symm)).comp φ) = (autHom σ).comp φ := by
    ext x; simp [autHom]
  rw [hcomp] at h
  exact h

theorem load_eq_zero_of_not_edge (f : F →g G) {e : Sym2 V} (he : e ∉ G.edgeSet) : load f e = 0 := by
  rw [load, card_eq_zero, filter_eq_empty_iff]
  intro e' he' heq
  rw [mem_edgeFinset] at he'
  exact he (heq ▸ f.map_mem_edgeSet he')

/-- **Edge-transitive bound.** If `G` is edge-transitive, `F → G`, `F ↛ H` and `F` has an edge, then
`|E(G)| ≤ |E(F)|·|G,H|`. -/
theorem nhf_edge_transitive [DecidableEq U]
    (htrans : ∀ e ∈ G.edgeSet, ∀ e' ∈ G.edgeSet, ∃ τ : G ≃g G, e.map τ = e')
    (φ : F →g G) (hF : IsEmpty (F →g H)) (hFe : F.edgeSet.Nonempty) :
    (G.edgeFinset.card : ℕ∞) ≤ F.edgeFinset.card * nhf G H := by
  classical
  have hFpos : 0 < F.edgeFinset.card := by
    obtain ⟨e, he⟩ := hFe; exact card_pos.mpr ⟨e, mem_edgeFinset.mpr he⟩
  obtain ⟨e₀, he₀⟩ := hFe
  have hGe : e₀.map φ ∈ G.edgeSet := φ.map_mem_edgeSet he₀
  set g₀ := e₀.map φ
  set c := totLoad φ g₀
  -- every edge of G has total load `c`
  have hc : ∀ e ∈ G.edgeSet, totLoad φ e = c := by
    intro e he
    obtain ⟨τ, hτ⟩ := htrans g₀ hGe e he
    rw [← hτ, totLoad_transfer]
  -- `|E(G)|·c = |Aut|·|E(F)|`
  have hsum : G.edgeFinset.card * c = Fintype.card (G ≃g G) * F.edgeFinset.card := by
    have : ∑ e ∈ G.edgeFinset, totLoad φ e = G.edgeFinset.card * c := by
      rw [sum_congr rfl (fun e he => hc e (mem_edgeFinset.mp he))]; simp
    rw [← this]
    unfold totLoad
    rw [sum_comm]
    simp_rw [← card_edgeFinset_eq_sum_load]
    simp
  -- every deletion set `S` making `G - S → H` satisfies `|Aut| ≤ c·|S|`
  have key : ∀ S : Finset (Sym2 V), Nonempty (G.deleteEdges ↑S →g H) →
      G.edgeFinset.card ≤ F.edgeFinset.card * S.card := by
    intro S ⟨ψ⟩
    have hhit : ∀ σ : G ≃g G, 1 ≤ ∑ e ∈ S, load ((autHom σ).comp φ) e := by
      intro σ
      rw [← card_pullEdges_eq_sum, Nat.one_le_iff_ne_zero, ← pos_iff_ne_zero, card_pos]
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      apply hF.false
      refine ψ.comp ((pullHom ((autHom σ).comp φ) S).comp ?_)
      refine ⟨id, fun {u v} huv => ?_⟩
      rw [deleteEdges_adj]
      refine ⟨huv, fun hmem => ?_⟩
      have : s(u, v) ∈ pullEdges ((autHom σ).comp φ) S := hmem
      rw [hne] at this; exact absurd this (Finset.notMem_empty _)
    have h1 : Fintype.card (G ≃g G) ≤ ∑ e ∈ S, totLoad φ e := by
      calc Fintype.card (G ≃g G) = ∑ _σ : G ≃g G, 1 := by simp
        _ ≤ ∑ σ : G ≃g G, ∑ e ∈ S, load ((autHom σ).comp φ) e := sum_le_sum fun σ _ => hhit σ
        _ = ∑ e ∈ S, totLoad φ e := by unfold totLoad; rw [sum_comm]
    have h2 : ∑ e ∈ S, totLoad φ e ≤ S.card * c := by
      calc ∑ e ∈ S, totLoad φ e ≤ ∑ _e ∈ S, c := by
            apply sum_le_sum; intro e _
            by_cases he : e ∈ G.edgeSet
            · exact (hc e he).le
            · unfold totLoad
              rw [sum_eq_zero (fun σ _ => load_eq_zero_of_not_edge _ he)]; exact Nat.zero_le _
        _ = S.card * c := by simp
    have hA : 0 < Fintype.card (G ≃g G) := Fintype.card_pos_iff.mpr ⟨RelIso.refl _⟩
    have h3 : Fintype.card (G ≃g G) * G.edgeFinset.card ≤
        Fintype.card (G ≃g G) * (F.edgeFinset.card * S.card) := by
      calc Fintype.card (G ≃g G) * G.edgeFinset.card
          ≤ S.card * c * G.edgeFinset.card := Nat.mul_le_mul_right _ (h1.trans h2)
        _ = S.card * (G.edgeFinset.card * c) := by ring
        _ = Fintype.card (G ≃g G) * (F.edgeFinset.card * S.card) := by rw [hsum]; ring
    exact Nat.le_of_mul_le_mul_left h3 hA
  by_cases htop : nhf G H = ⊤
  · rw [htop, ENat.mul_top (by exact_mod_cast hFpos.ne')]; exact le_top
  · obtain ⟨S, hS, hcard⟩ := exists_nhf_eq htop
    rw [← hcard]
    exact_mod_cast key S hS

end transitive

end NonHom
