import NonHom.OddCycles
import NonHom.Turan

/-!
# Results from `open_problems/` (README.md and sage_a1_5/README.md)

* Theorem 2 (quantitative Hedetniemi): `|G×H,K| ≤ min(2|E(H)|·|G,K|, 2|E(G)|·|H,K|)`.
* Theorem 3, upper bound: `|C_p×C_q,K₂| ≤ 2p` for odd `p`, `q`.
* `|C_n,K₂| = 1` for odd `n ≥ 3`.
* Sage result 1: `|K_n,H| = C(n,2) - ⌊n²/4⌋` for every triangle-free `H` with an edge.
-/

open SimpleGraph Finset

namespace NonHom

variable {V W X : Type*}

/-- The tensor (categorical) product `G × H`. -/
def tensor (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V × W) where
  Adj x y := G.Adj x.1 y.1 ∧ H.Adj x.2 y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

instance {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (tensor G H).Adj := fun x y => inferInstanceAs (Decidable (_ ∧ _))

def tensorFst (G : SimpleGraph V) (H : SimpleGraph W) : tensor G H →g G := ⟨Prod.fst, fun h => h.1⟩
def tensorSnd (G : SimpleGraph V) (H : SimpleGraph W) : tensor G H →g H := ⟨Prod.snd, fun h => h.2⟩

def tensorComm (G : SimpleGraph V) (H : SimpleGraph W) : tensor G H ≃g tensor H G where
  toEquiv := Equiv.prodComm V W
  map_rel_iff' := by intro a b; simp [tensor, and_comm]

/-- An edgeless graph maps to any graph with a vertex. -/
theorem nhf_eq_zero_of_edgeless {G : SimpleGraph V} {K : SimpleGraph X} [Nonempty X]
    (h : G.edgeSet = ∅) : nhf G K = 0 := by
  apply nhf_eq_zero_of_hom
  refine ⟨fun _ => Classical.arbitrary X, fun {a b} hab => ?_⟩
  have : s(a, b) ∈ G.edgeSet := hab
  rw [h] at this; exact absurd this (Set.notMem_empty _)

/-- Version of Lemma `lem:nhf_bound` with any upper bound on `μ(f)`. -/
theorem nhf_le_of_mu_le [Fintype V] [DecidableEq W] [Nonempty X]
    {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} {K : SimpleGraph X}
    (f : G →g H) (c : ℕ) (hc : mu f ≤ c) : nhf G K ≤ (c : ℕ∞) * nhf H K := by
  by_cases hG : G.edgeSet.Nonempty
  · refine (nhf_le_mu_mul f hG).trans ?_
    gcongr
  · rw [Set.not_nonempty_iff_eq_empty] at hG
    rw [nhf_eq_zero_of_edgeless hG]; exact zero_le

/-- Isomorphisms preserve `|·,K|` (from edge-injectivity, Proposition `prop:monotone`(3)). -/
theorem nhf_le_of_iso [Fintype V] [DecidableEq W] {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : SimpleGraph W} {K : SimpleGraph X} (e : G ≃g H) : nhf G K ≤ nhf H K :=
  nhf_le_of_edge_injective e.toHom fun _ _ _ _ h => Sym2.map.injective e.injective h

section tensor

variable [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]

/-- The projection `G×H → G` has `μ ≤ 2|E(H)|`. -/
theorem mu_tensorFst_le : mu (tensorFst G H) ≤ 2 * H.edgeFinset.card := by
  apply Finset.sup_le
  intro e he
  rw [mem_edgeFinset] at he
  induction e using Sym2.ind with
  | _ x y =>
    have hxy : x.1 ≠ y.1 := he.1.ne
    show load (tensorFst G H) s(x.1, y.1) ≤ _
    rw [load_eq_card_darts _ hxy, ← dart_card_eq_twice_card_edges, ← card_univ]
    apply card_le_card_of_injOn (fun d => (⟨(d.fst.2, d.snd.2), d.adj.2⟩ : H.Dart))
    · intro _ _; exact mem_coe.mpr (mem_univ _)
    · intro d₁ h₁ d₂ h₂ h
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h₁ h₂
      simp only [Dart.mk.injEq, Prod.mk.injEq] at h
      apply Dart.ext
      apply Prod.ext <;> apply Prod.ext
      · exact h₁.1.trans h₂.1.symm
      · exact h.1
      · exact h₁.2.trans h₂.2.symm
      · exact h.2

/-- **Theorem 2** (quantitative Hedetniemi). For `K` with at least one vertex,
`|G×H,K| ≤ 2|E(H)|·|G,K|` and `|G×H,K| ≤ 2|E(G)|·|H,K|`. -/
theorem hedetniemi_bound {K : SimpleGraph X} [Nonempty X] :
    nhf (tensor G H) K ≤ ((2 * H.edgeFinset.card : ℕ) : ℕ∞) * nhf G K ∧
    nhf (tensor G H) K ≤ ((2 * G.edgeFinset.card : ℕ) : ℕ∞) * nhf H K := by
  refine ⟨nhf_le_of_mu_le (tensorFst G H) _ mu_tensorFst_le, ?_⟩
  have h1 := nhf_le_of_mu_le (K := K) (tensorFst H G) _ (mu_tensorFst_le (G := H) (H := G))
  have h2 : nhf (tensor G H) K ≤ nhf (tensor H G) K :=
    nhf_le_of_iso (tensorComm G H)
  exact h2.trans h1

end tensor

/-- `|C_n,K₂| ≤ 1`: deleting the edge `{n-1, 0}` leaves a path. -/
theorem nhf_cycle_K2_le_one (k : ℕ) : nhf (cycleGraph (k + 3)) (⊤ : SimpleGraph (Fin 2)) ≤ 1 := by
  have h := nhf_le_card (G := cycleGraph (k + 3)) (H := (⊤ : SimpleGraph (Fin 2)))
    {s(0, Fin.last (k + 2))} ⟨⟨fun i => ⟨i.val % 2, Nat.mod_lt _ (by norm_num)⟩, by
      intro u v huv
      rw [deleteEdges_adj] at huv
      obtain ⟨hadj, hnot⟩ := huv
      have h := cycle_adj_val hadj
      simp only [coe_singleton, Set.mem_singleton_iff, Sym2.eq_iff, Fin.ext_iff, Fin.val_zero,
        Fin.val_last] at hnot
      simp only [top_adj, ne_eq, Fin.mk.injEq]
      omega⟩⟩
  simpa using h

/-- `|C_n,K₂| = 1` for odd `n ≥ 3`. -/
theorem nhf_cycle_K2_odd (k : ℕ) (hodd : Odd (k + 3)) :
    nhf (cycleGraph (k + 3)) (⊤ : SimpleGraph (Fin 2)) = 1 := by
  apply le_antisymm (nhf_cycle_K2_le_one k)
  rw [ENat.one_le_iff_ne_zero]
  intro h0
  obtain ⟨g⟩ := nhf_eq_zero_iff.mp h0
  have h3 := chromaticNumber_cycleGraph_of_odd (k + 3) (by omega) hodd
  have := (Colorable.of_hom g (by simpa using colorable_of_fintype (⊤ : SimpleGraph (Fin 2)))).chromaticNumber_le
  rw [h3] at this
  exact absurd this (by decide)

/-- **Theorem 3, upper bound**: `|C_p × C_q, K₂| ≤ 2p` for odd `q ≥ 3` (any `p ≥ 3`). -/
theorem nhf_tensor_cycles_le (k l : ℕ) (hq : Odd (l + 3)) :
    nhf (tensor (cycleGraph (k + 3)) (cycleGraph (l + 3))) (⊤ : SimpleGraph (Fin 2)) ≤
      ((2 * (k + 3) : ℕ) : ℕ∞) := by
  have h := (hedetniemi_bound (G := cycleGraph (k + 3)) (H := cycleGraph (l + 3))
    (K := (⊤ : SimpleGraph (Fin 2)))).2
  rwa [card_edges_cycle, nhf_cycle_K2_odd l hq, mul_one] at h

/-! ### Sage result 1 -/

theorem cliqueFree_of_hom {G : SimpleGraph V} {H : SimpleGraph W} [DecidableEq W]
    (f : G →g H) {n : ℕ} (h : H.CliqueFree n) : G.CliqueFree n := by
  intro s hs
  apply h (s.image f)
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [coe_image, Set.mem_image, mem_coe] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have hab : a ≠ b := fun e => hxy (e ▸ rfl)
    exact f.map_rel (hs.isClique ha hb hab)
  · rw [card_image_of_injOn, hs.card_eq]
    intro a ha b hb hab
    by_contra hne
    exact (f.map_rel (hs.isClique ha hb hne)).ne hab

/-- **Sage result 1**: for every triangle-free `H` with an edge, `|K_n,H| = C(n,2) - ⌊n²/4⌋`. -/
theorem nhf_top_triangleFree (n : ℕ) {H : SimpleGraph W} [DecidableEq W] (hH : H.CliqueFree 3)
    {u v : W} (huv : H.Adj u v) :
    nhf (⊤ : SimpleGraph (Fin n)) H = ((n.choose 2 - n ^ 2 / 4 : ℕ) : ℕ∞) := by
  have hK2 : (⊤ : SimpleGraph (Fin 2)) →g H :=
    ⟨![u, v], by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [huv, huv.symm]⟩
  have eq1 := nhf_top_top n 2 (by norm_num)
  rw [turanNumber_two] at eq1
  apply le_antisymm
  · rw [← eq1]; exact nhf_le_of_hom_target hK2
  · apply le_nhf
    intro S ⟨f⟩
    have hcf := cliqueFree_of_hom f hH
    have hle := hcf.card_edgeFinset_le
    rw [Fintype.card_fin, turanNumber_two] at hle
    have hE : ((⊤ : SimpleGraph (Fin n)).deleteEdges ↑S).edgeFinset =
        (⊤ : SimpleGraph (Fin n)).edgeFinset \ S := edgeFinset_deleteEdges S
    rw [hE] at hle
    have := card_le_card_sdiff_add_card (s := (⊤ : SimpleGraph (Fin n)).edgeFinset) (t := S)
    rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin] at this
    norm_cast
    omega

end NonHom
