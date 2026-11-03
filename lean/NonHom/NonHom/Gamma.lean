import NonHom.NHF

/-!
# The concentration parameter `γ(G,H)`

Section 3 of the paper: Proposition `prop:pigeonhole`, Lemmas `lem:gamma_identity`,
`lem:gamma_pos`, `lem:gamma_mult`, `lem:nhf_bound`, `lem:two_sided`, `lem:gamma_mono`,
and Proposition `prop:gamma_Kn`.
-/

open SimpleGraph Finset

namespace NonHom

variable {V W X : Type*}

section basic

variable [Fintype V] [DecidableEq W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W}

theorem gamma_le_mu (f : G →g H) : gamma G H ≤ mu f :=
  iInf_le (fun f : G →g H => (mu f : ℕ∞)) f

theorem le_gamma {k : ℕ∞} (h : ∀ f : G →g H, k ≤ mu f) : k ≤ gamma G H :=
  le_iInf h

theorem gamma_eq_top_iff : gamma G H = ⊤ ↔ IsEmpty (G →g H) := by
  constructor
  · intro h
    refine ⟨fun f => ?_⟩
    have := gamma_le_mu f
    rw [h] at this
    exact absurd (top_le_iff.mp this) (ENat.coe_ne_top _)
  · intro h
    simp [gamma, iInf_of_empty]

/-- `γ` is attained by some homomorphism when one exists. -/
theorem exists_gamma_eq (h : Nonempty (G →g H)) :
    ∃ f : G →g H, (mu f : ℕ∞) = gamma G H := by
  have hne : (Set.range fun f : G →g H => (mu f : ℕ∞)).Nonempty := Set.range_nonempty _
  obtain ⟨f, hf⟩ := csInf_mem hne
  exact ⟨f, hf⟩

theorem one_le_load_map (f : G →g H) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    1 ≤ load f (e.map f) := by
  rw [load, Nat.one_le_iff_ne_zero, ← pos_iff_ne_zero, card_pos]
  exact ⟨e, by simp [he]⟩

/-- Lemma `lem:gamma_pos`: `μ(f) ≥ 1` whenever `G` has an edge. -/
theorem one_le_mu (f : G →g H) (hG : G.edgeSet.Nonempty) : 1 ≤ mu f := by
  obtain ⟨e, he⟩ := hG
  exact (one_le_load_map f he).trans (load_le_mu f _)

/-- Lemma `lem:gamma_pos`: `γ(G,H) ≥ 1` whenever `G` has an edge. -/
theorem one_le_gamma (hG : G.edgeSet.Nonempty) : 1 ≤ gamma G H :=
  le_gamma fun f => by exact_mod_cast one_le_mu f hG

/-- `|E(G)| = ∑_{e ∈ E(H)} load f e` (the loads partition the edges of `G`). -/
theorem card_edgeFinset_eq_sum_load [Fintype W] [DecidableRel H.Adj] (f : G →g H) :
    G.edgeFinset.card = ∑ e ∈ H.edgeFinset, load f e := by
  unfold load
  apply card_eq_sum_card_fiberwise
  intro e he
  rw [coe_edgeFinset] at he ⊢
  exact f.map_mem_edgeSet he

/-- Proposition `prop:pigeonhole`, per homomorphism: `|E(G)| ≤ |E(H)|·μ(f)`. -/
theorem card_edgeFinset_le_mul_mu [Fintype W] [DecidableRel H.Adj] (f : G →g H) :
    G.edgeFinset.card ≤ H.edgeFinset.card * mu f := by
  rw [card_edgeFinset_eq_sum_load f]
  calc ∑ e ∈ H.edgeFinset, load f e ≤ ∑ _e ∈ H.edgeFinset, mu f :=
        sum_le_sum fun e _ => load_le_mu f e
    _ = H.edgeFinset.card * mu f := by simp

/-- Proposition `prop:pigeonhole`: `γ(G,H) ≥ ⌈|E(G)| / |E(H)|⌉` (written with
`⌈a/b⌉ = (a + b - 1) / b`). -/
theorem ceil_div_le_gamma [Fintype W] [DecidableRel H.Adj] (hH : H.edgeFinset.card ≠ 0) :
    (((G.edgeFinset.card + H.edgeFinset.card - 1) / H.edgeFinset.card : ℕ) : ℕ∞) ≤ gamma G H := by
  apply le_gamma
  intro f
  have h := card_edgeFinset_le_mul_mu f
  have hpos : 0 < H.edgeFinset.card := Nat.pos_of_ne_zero hH
  norm_cast
  rw [Nat.div_le_iff_le_mul_add_pred hpos]
  calc G.edgeFinset.card + H.edgeFinset.card - 1
      ≤ H.edgeFinset.card * mu f + H.edgeFinset.card - 1 := by omega
    _ = H.edgeFinset.card * mu f + (H.edgeFinset.card - 1) := by omega

/-- Proposition `prop:pigeonhole`, multiplicative form: `|E(G)| ≤ |E(H)| · γ(G,H)`. -/
theorem card_edgeFinset_le_mul_gamma [Fintype W] [DecidableRel H.Adj] (h : Nonempty (G →g H)) :
    (G.edgeFinset.card : ℕ∞) ≤ H.edgeFinset.card * gamma G H := by
  obtain ⟨f, hf⟩ := exists_gamma_eq h
  rw [← hf]
  exact_mod_cast card_edgeFinset_le_mul_mu f

end basic

section identity

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem load_id (e : Sym2 V) (he : e ∈ G.edgeSet) : load (Hom.id : G →g G) e = 1 := by
  unfold load
  rw [card_eq_one]
  refine ⟨e, ?_⟩
  ext e'
  simp only [mem_filter, mem_edgeFinset, Hom.coe_id, Sym2.map_id', id_eq, mem_singleton]
  constructor
  · rintro ⟨_, rfl⟩; rfl
  · rintro rfl; exact ⟨he, rfl⟩

theorem mu_id (hG : G.edgeSet.Nonempty) : mu (Hom.id : G →g G) = 1 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro e he
    rw [mem_edgeFinset] at he
    have : Sym2.map (⇑(Hom.id : G →g G)) e = e := by simp [Hom.coe_id]
    rw [this]
    exact (load_id e he).le
  · exact one_le_mu _ hG

/-- Lemma `lem:gamma_identity`: `γ(G,G) = 1` whenever `G` has an edge. -/
theorem gamma_self (hG : G.edgeSet.Nonempty) : gamma G G = 1 :=
  le_antisymm (by simpa [mu_id hG] using gamma_le_mu (Hom.id : G →g G)) (one_le_gamma hG)

end identity

section mult

variable [Fintype V] [DecidableEq W] [Fintype W] [DecidableEq X]
  {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]
  {K : SimpleGraph X}

theorem load_comp_le (f : G →g H) (g : H →g K) (e : Sym2 X) :
    load (g.comp f) e ≤ load g e * mu f := by
  unfold load
  have hmaps : ∀ e' ∈ G.edgeFinset.filter (fun e' => e'.map (g.comp f) = e),
      e'.map f ∈ H.edgeFinset.filter (fun e'' => e''.map g = e) := by
    intro e' he'
    rw [mem_filter, mem_edgeFinset] at he' ⊢
    refine ⟨f.map_mem_edgeSet he'.1, ?_⟩
    rw [Sym2.map_map]
    exact he'.2
  rw [card_eq_sum_card_fiberwise hmaps]
  calc ∑ e'' ∈ H.edgeFinset.filter (fun e'' => e''.map g = e),
        ((G.edgeFinset.filter fun e' => e'.map (g.comp f) = e).filter
          fun e' => e'.map f = e'').card
      ≤ ∑ _e'' ∈ H.edgeFinset.filter (fun e'' => e''.map g = e), mu f := by
        apply sum_le_sum
        intro e'' _
        refine le_trans ?_ (load_le_mu f e'')
        unfold load
        apply card_le_card
        intro e' he'
        simp only [mem_filter] at he' ⊢
        exact ⟨he'.1.1, he'.2⟩
    _ = _ := by simp

theorem mu_comp_le (f : G →g H) (g : H →g K) : mu (g.comp f) ≤ mu f * mu g := by
  apply Finset.sup_le
  intro e' he'
  calc load (g.comp f) (e'.map (g.comp f)) ≤ load g (e'.map (g.comp f)) * mu f :=
        load_comp_le f g _
    _ ≤ mu g * mu f := by
        apply Nat.mul_le_mul_right
        have : e'.map (g.comp f) = (e'.map f).map g := by rw [Sym2.map_map]; rfl
        rw [this]
        exact load_le_mu g _
    _ = mu f * mu g := mul_comm _ _

/-- Lemma `lem:gamma_mult` (multiplicativity): if `G → H → K` then
`γ(G,K) ≤ γ(G,H)·γ(H,K)`. -/
theorem gamma_comp_le (hGH : Nonempty (G →g H)) (hHK : Nonempty (H →g K)) :
    gamma G K ≤ gamma G H * gamma H K := by
  obtain ⟨f, hf⟩ := exists_gamma_eq hGH
  obtain ⟨g, hg⟩ := exists_gamma_eq hHK
  rw [← hf, ← hg]
  refine (gamma_le_mu (g.comp f)).trans ?_
  exact_mod_cast mu_comp_le f g

end mult

section nhfBound

variable [Fintype V] [DecidableEq W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} {K : SimpleGraph X}

/-- Lemma `lem:nhf_bound`: if `G → H` and `G` has an edge then `|G,K| ≤ γ(G,H)·|H,K|`. -/
theorem nhf_le_gamma_mul (hGH : Nonempty (G →g H)) (hG : G.edgeSet.Nonempty) :
    nhf G K ≤ gamma G H * nhf H K := by
  obtain ⟨f, hf⟩ := exists_gamma_eq hGH
  rw [← hf]
  exact nhf_le_mu_mul f hG

end nhfBound

section twoSided

variable [Fintype V] [Fintype X] [DecidableEq W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} {K : SimpleGraph X}
  [DecidableRel K.Adj]

/-- Lemma `lem:two_sided`: if `G → H` and `K → H` then
`|G,K| ≤ γ(G,H)·|H,K|` and `|K,G| ≤ γ(K,H)·|H,G|`, hence
`m(G,K) ≤ max(γ(G,H)·|H,K|, γ(K,H)·|H,G|)`. -/
theorem two_sided (hGH : Nonempty (G →g H)) (hKH : Nonempty (K →g H))
    (hG : G.edgeSet.Nonempty) (hK : K.edgeSet.Nonempty) :
    nhf G K ≤ gamma G H * nhf H K ∧ nhf K G ≤ gamma K H * nhf H G ∧
      msym G K ≤ max (gamma G H * nhf H K) (gamma K H * nhf H G) :=
  ⟨nhf_le_gamma_mul hGH hG, nhf_le_gamma_mul hKH hK,
    max_le_max (nhf_le_gamma_mul hGH hG) (nhf_le_gamma_mul hKH hK)⟩

end twoSided

section mono

variable [Fintype V] [DecidableEq W] [DecidableEq X]
  {G : SimpleGraph V} [DecidableRel G.Adj] {H₁ : SimpleGraph W} {H₂ : SimpleGraph X}

/-- Composing with an injective homomorphism of targets does not change loads. -/
theorem load_comp_injective (f : G →g H₁) (ι : H₁ →g H₂) (hι : Function.Injective ι)
    (e : Sym2 W) : load (ι.comp f) (e.map ι) = load f e := by
  unfold load
  congr 1
  ext e'
  simp only [mem_filter, Hom.coe_comp, ← Sym2.map_map]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Sym2.map.injective hι h2⟩
  · rintro ⟨h1, rfl⟩
    exact ⟨h1, rfl⟩

theorem mu_comp_injective (f : G →g H₁) (ι : H₁ →g H₂) (hι : Function.Injective ι) :
    mu (ι.comp f) = mu f := by
  unfold mu
  apply sup_congr rfl
  intro e' _
  have : Sym2.map (⇑(ι.comp f)) e' = Sym2.map (⇑ι) (Sym2.map (⇑f) e') := by
    rw [Sym2.map_map, Hom.coe_comp]
  rw [this, load_comp_injective f ι hι]

/-- Lemma `lem:gamma_mono` (monotonicity in the target): if `H₁` embeds in `H₂` via an injective
homomorphism (e.g. `H₁ ⊆ H₂`), then `γ(G,H₂) ≤ γ(G,H₁)`. -/
theorem gamma_le_of_injective_hom (ι : H₁ →g H₂) (hι : Function.Injective ι) :
    gamma G H₂ ≤ gamma G H₁ := by
  apply le_gamma
  intro f
  rw [← mu_comp_injective f ι hι]
  exact gamma_le_mu _

end mono

section subgraphMono

variable [Fintype V] [DecidableEq W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {H₁ H₂ : SimpleGraph W}

/-- Lemma `lem:gamma_mono` for a subgraph `H₁ ≤ H₂` on the same vertex set. -/
theorem gamma_anti_target (h : H₁ ≤ H₂) : gamma G H₂ ≤ gamma G H₁ :=
  gamma_le_of_injective_hom (Hom.ofLE h) fun _ _ hxy => hxy

end subgraphMono

section complete

/-- Proposition `prop:gamma_Kn`, first half: for `2 ≤ n ≤ m`, `γ(K_n,K_m) = 1`. -/
theorem gamma_top_top_eq_one {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) :
    gamma (⊤ : SimpleGraph (Fin n)) (⊤ : SimpleGraph (Fin m)) = 1 := by
  have hG : (⊤ : SimpleGraph (Fin n)).edgeSet.Nonempty :=
    ⟨s(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.ext_iff]⟩
  apply le_antisymm _ (one_le_gamma hG)
  let ι : (⊤ : SimpleGraph (Fin n)) →g (⊤ : SimpleGraph (Fin m)) :=
    ⟨Fin.castLE hnm, fun h => by simpa [Fin.ext_iff] using h⟩
  have hinj : Function.Injective ι := Fin.castLE_injective hnm
  refine (gamma_le_mu ι).trans ?_
  exact_mod_cast mu_le_one_of_edge_injective ι fun e₁ _ e₂ _ h => Sym2.map.injective hinj h

/-- Proposition `prop:gamma_Kn`, second half: for `n > m`, `γ(K_n,K_m) = ⊤` (no homomorphism). -/
theorem gamma_top_top_eq_top {n m : ℕ} (hmn : m < n) :
    gamma (⊤ : SimpleGraph (Fin n)) (⊤ : SimpleGraph (Fin m)) = ⊤ := by
  rw [gamma_eq_top_iff]
  refine ⟨fun f => ?_⟩
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    exact (f.map_rel (show (⊤ : SimpleGraph (Fin n)).Adj a b from hne)) hab
  have := Fintype.card_le_of_injective f hinj
  simp at this
  omega

end complete

end NonHom
