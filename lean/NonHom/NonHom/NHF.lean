import NonHom.Defs

/-!
# Basic properties of the non-homomorphism factor

Proposition `prop:monotone` of the paper (three parts), plus the general
"load" bound (Lemma `lem:nhf_bound`) in the form `|G,K| ≤ μ(f)·|H,K|`.
-/

open SimpleGraph Finset

namespace NonHom

variable {V W X : Type*}

section basic

variable {G : SimpleGraph V} {H : SimpleGraph W}

theorem nhf_le_card (S : Finset (Sym2 V)) (h : Nonempty (G.deleteEdges ↑S →g H)) :
    nhf G H ≤ S.card :=
  sInf_le ⟨S, h, rfl⟩

theorem nhf_eq_zero_of_hom (f : G →g H) : nhf G H = 0 := by
  apply le_antisymm _ bot_le
  have := nhf_le_card (G := G) (H := H) ∅ ⟨by simpa [deleteEdges_empty] using f⟩
  simpa using this

theorem le_nhf {k : ℕ∞} (h : ∀ S : Finset (Sym2 V), Nonempty (G.deleteEdges ↑S →g H) → k ≤ S.card) :
    k ≤ nhf G H := by
  apply le_sInf
  rintro _ ⟨S, hS, rfl⟩
  exact h S hS

/-- When `|G,H|` is finite it is attained by some edge set. -/
theorem exists_nhf_eq (h : nhf G H ≠ ⊤) :
    ∃ S : Finset (Sym2 V), Nonempty (G.deleteEdges ↑S →g H) ∧ (S.card : ℕ∞) = nhf G H := by
  have hne : (nhfSet G H).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    exact h (by simp [nhf, hcon])
  exact csInf_mem hne

theorem nhf_eq_zero_iff : nhf G H = 0 ↔ Nonempty (G →g H) := by
  constructor
  · intro h0
    obtain ⟨S, hS, hcard⟩ := exists_nhf_eq (G := G) (H := H) (by rw [h0]; exact ENat.zero_ne_top)
    rw [h0] at hcard
    have : S = ∅ := by simpa using hcard
    subst this
    simpa [deleteEdges_empty] using hS
  · rintro ⟨f⟩
    exact nhf_eq_zero_of_hom f

/-- Proposition `prop:monotone` (1): `H₁ → H₂` implies `|G,H₂| ≤ |G,H₁|`. -/
theorem nhf_le_of_hom_target {H₁ : SimpleGraph W} {H₂ : SimpleGraph X} (g : H₁ →g H₂) :
    nhf G H₂ ≤ nhf G H₁ := by
  apply le_nhf
  intro S ⟨f⟩
  exact nhf_le_card S ⟨g.comp f⟩

/-- Proposition `prop:monotone` (2): homomorphically equivalent targets give equal factors. -/
theorem nhf_eq_of_hom_equiv {H₁ : SimpleGraph W} {H₂ : SimpleGraph X}
    (g : H₁ →g H₂) (g' : H₂ →g H₁) : nhf G H₁ = nhf G H₂ :=
  le_antisymm (nhf_le_of_hom_target g') (nhf_le_of_hom_target g)

end basic

section transfer

variable [Fintype V] [DecidableEq W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} {K : SimpleGraph X}

/-- The edges of `G` whose image under `f` lies in `S`. -/
def pullEdges (f : G →g H) (S : Finset (Sym2 W)) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => e.map f ∈ S

/-- A homomorphism `f : G → H` restricts to `G - f⁻¹(S) → H - S`. -/
def pullHom (f : G →g H) (S : Finset (Sym2 W)) :
    G.deleteEdges ↑(pullEdges f S) →g H.deleteEdges ↑S where
  toFun := f
  map_rel' := by
    intro u v huv
    rw [deleteEdges_adj] at huv ⊢
    obtain ⟨hadj, hnot⟩ := huv
    refine ⟨f.map_rel hadj, fun hmem => hnot ?_⟩
    simp only [pullEdges, coe_filter, Set.mem_ofPred_eq, mem_edgeFinset, mem_edgeSet]
    exact ⟨hadj, by simpa using hmem⟩

theorem nhf_le_card_pullEdges (f : G →g H) (S : Finset (Sym2 W))
    (hS : Nonempty (H.deleteEdges ↑S →g K)) : nhf G K ≤ (pullEdges f S).card :=
  nhf_le_card _ ⟨hS.some.comp (pullHom f S)⟩

theorem card_pullEdges_eq_sum (f : G →g H) (S : Finset (Sym2 W)) :
    (pullEdges f S).card = ∑ e ∈ S, load f e := by
  unfold pullEdges load
  rw [card_eq_sum_card_fiberwise (f := fun e' => Sym2.map f e') (t := S)]
  · apply sum_congr rfl
    intro e he
    congr 1
    ext e'
    simp only [mem_filter, mem_edgeFinset]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ he⟩, h3⟩
  · intro e' he'
    simp only [coe_filter, Set.mem_ofPred_eq] at he'
    exact he'.2

theorem load_le_mu (f : G →g H) (e : Sym2 W) : load f e ≤ mu f := by
  by_cases h : (G.edgeFinset.filter fun e' => e'.map f = e).Nonempty
  · obtain ⟨e', he'⟩ := h
    rw [mem_filter] at he'
    rw [← he'.2]
    exact le_sup (f := fun e' => load f (e'.map f)) he'.1
  · rw [not_nonempty_iff_eq_empty] at h
    simp [load, h]

theorem card_pullEdges_le (f : G →g H) (S : Finset (Sym2 W)) :
    (pullEdges f S).card ≤ S.card * mu f := by
  rw [card_pullEdges_eq_sum]
  calc ∑ e ∈ S, load f e ≤ ∑ _e ∈ S, mu f := sum_le_sum fun e _ => load_le_mu f e
    _ = S.card * mu f := by simp

/-- Proposition `prop:monotone` (3): an edge-injective homomorphism `G₁ → G₂` gives
`|G₁,H| ≤ |G₂,H|`. -/
theorem nhf_le_of_edge_injective (f : G →g H)
    (hinj : ∀ e₁ ∈ G.edgeSet, ∀ e₂ ∈ G.edgeSet, e₁.map f = e₂.map f → e₁ = e₂) :
    nhf G K ≤ nhf H K := by
  by_cases htop : nhf H K = ⊤
  · rw [htop]; exact le_top
  obtain ⟨S, hS, hcard⟩ := exists_nhf_eq htop
  rw [← hcard]
  refine (nhf_le_card_pullEdges f S hS).trans ?_
  norm_cast
  apply card_le_card_of_injOn (fun e => e.map f)
  · intro e he
    simp only [pullEdges, coe_filter, Set.mem_ofPred_eq, mem_edgeFinset] at he
    exact he.2
  · intro e₁ h₁ e₂ h₂ h
    simp only [pullEdges, coe_filter, Set.mem_ofPred_eq, mem_edgeFinset] at h₁ h₂
    exact hinj e₁ h₁.1 e₂ h₂.1 h

/-- Edge-injective homomorphisms have `μ ≤ 1`. -/
theorem mu_le_one_of_edge_injective (f : G →g H)
    (hinj : ∀ e₁ ∈ G.edgeSet, ∀ e₂ ∈ G.edgeSet, e₁.map f = e₂.map f → e₁ = e₂) :
    mu f ≤ 1 := by
  apply Finset.sup_le
  intro e he
  rw [mem_edgeFinset] at he
  unfold load
  apply card_le_one.mpr
  intro a ha b hb
  rw [mem_filter, mem_edgeFinset] at ha hb
  exact hinj a ha.1 b hb.1 (ha.2.trans hb.2.symm)

/-- Lemma `lem:nhf_bound`, per homomorphism: `|G,K| ≤ μ(f)·|H,K|`, provided `G` has an edge. -/
theorem nhf_le_mu_mul (f : G →g H) (hG : G.edgeSet.Nonempty) :
    nhf G K ≤ (mu f : ℕ∞) * nhf H K := by
  have hmu : (mu f : ℕ∞) ≠ 0 := by
    obtain ⟨e, he⟩ := hG
    have : 1 ≤ load f (e.map f) := by
      apply Nat.one_le_iff_ne_zero.mpr
      rw [load, ← pos_iff_ne_zero, card_pos]
      exact ⟨e, by simp [he]⟩
    have := this.trans (load_le_mu f _)
    exact_mod_cast (by omega : mu f ≠ 0)
  by_cases htop : nhf H K = ⊤
  · rw [htop, ENat.mul_top hmu]; exact le_top
  obtain ⟨S, hS, hcard⟩ := exists_nhf_eq htop
  rw [← hcard]
  refine (nhf_le_card_pullEdges f S hS).trans ?_
  rw [mul_comm]
  exact_mod_cast card_pullEdges_le f S

end transfer

end NonHom
