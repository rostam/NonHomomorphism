import NonHom.Regular

/-!
# The Petersen graph

* `|P,K₂| = 3` (Observation `obs:PK2`), proved via the twelve 5-cycles of `P`.
* `|P,K_m| = 0` for `m ≥ 3`.
* `γ(P,K₃) = 6` (Observation `obs:petersen_exceed`, via Theorem `thm:d_regular`).
-/

open SimpleGraph Finset

namespace NonHom

/-- Petersen graph on `Fin 10`: outer 5-cycle `0..4`, spokes `i ~ i+5`, inner pentagram. -/
def petersenAdj (a b : Fin 10) : Prop :=
  (a.val < 5 ∧ b.val < 5 ∧ (b.val = (a.val + 1) % 5 ∨ a.val = (b.val + 1) % 5)) ∨
  (a.val < 5 ∧ b.val = a.val + 5) ∨ (b.val < 5 ∧ a.val = b.val + 5) ∨
  (5 ≤ a.val ∧ 5 ≤ b.val ∧ (b.val - 5 = (a.val - 5 + 2) % 5 ∨ a.val - 5 = (b.val - 5 + 2) % 5))

instance : DecidableRel petersenAdj := fun a b => by unfold petersenAdj; infer_instance

def petersen : SimpleGraph (Fin 10) where
  Adj a b := petersenAdj a b
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

instance : DecidableRel petersen.Adj := fun a b => inferInstanceAs (Decidable (petersenAdj a b))

theorem petersen_regular : petersen.IsRegularOfDegree 3 := by
  intro v
  rw [← card_neighborFinset_eq_degree]
  have : ∀ v : Fin 10, (univ.filter fun w => petersen.Adj v w).card = 3 := by decide +kernel
  rw [← this v]
  congr 1
  ext w
  simp

/-! ### `|P,K₂| = 3` -/

/-- The twelve 5-cycles of the Petersen graph. -/
def pcyc : Fin 12 → Fin 5 → Fin 10 :=
  ![![0,1,2,3,4], ![0,1,2,7,5], ![0,1,6,8,5], ![0,1,6,9,4], ![0,4,3,8,5], ![0,4,9,7,5],
   ![1,2,3,8,6], ![1,2,7,9,6], ![2,3,4,9,7], ![2,3,8,5,7], ![3,4,9,6,8], ![5,7,9,6,8]]

/-- The fifteen edges of the Petersen graph. -/
def pedge : Fin 15 → Fin 10 × Fin 10 :=
  ![(0,1),(0,4),(0,5),(1,2),(1,6),(2,3),(2,7),(3,4),(3,8),(4,9),(5,7),(5,8),(6,8),(6,9),(7,9)]

set_option maxRecDepth 100000 in
theorem pcyc_adj : ∀ c : Fin 12, ∀ t : Fin 5, petersen.Adj (pcyc c t) (pcyc c (t + 1)) := by decide +kernel

theorem pedge_complete : ∀ u v : Fin 10, petersen.Adj u v →
    ∃ k : Fin 15, (u = (pedge k).1 ∧ v = (pedge k).2) ∨ (u = (pedge k).2 ∧ v = (pedge k).1) := by
  decide +kernel

/-- Any two edges miss some 5-cycle. -/
theorem pcyc_avoid : ∀ i j : Fin 15, ∃ c : Fin 12, ∀ t : Fin 5,
    ¬((pcyc c t = (pedge i).1 ∧ pcyc c (t + 1) = (pedge i).2) ∨
      (pcyc c t = (pedge i).2 ∧ pcyc c (t + 1) = (pedge i).1)) ∧
    ¬((pcyc c t = (pedge j).1 ∧ pcyc c (t + 1) = (pedge j).2) ∨
      (pcyc c t = (pedge j).2 ∧ pcyc c (t + 1) = (pedge j).1)) := by
  decide +kernel

theorem no_odd_five (g : Fin 5 → Fin 2) (h : ∀ t : Fin 5, g t ≠ g (t + 1)) : False := by
  revert g; decide +kernel

theorem subset_pair_of_card_le_two {α : Type*} [DecidableEq α] [Inhabited α] (S : Finset α)
    (h : S.card ≤ 2) : ∃ a b, S ⊆ {a, b} := by
  rcases (by omega : S.card = 0 ∨ S.card = 1 ∨ S.card = 2) with h | h | h
  · rw [card_eq_zero] at h; exact ⟨default, default, by simp [h]⟩
  · obtain ⟨a, rfl⟩ := card_eq_one.mp h; exact ⟨a, a, by simp⟩
  · obtain ⟨a, b, -, rfl⟩ := card_eq_two.mp h; exact ⟨a, b, subset_refl _⟩

/-- Index of a Petersen edge equal to `a`, if any. -/
theorem pedge_index (a : Sym2 (Fin 10)) : ∃ k : Fin 15, ∀ u v : Fin 10, petersen.Adj u v →
    s(u, v) = a → (u = (pedge k).1 ∧ v = (pedge k).2) ∨ (u = (pedge k).2 ∧ v = (pedge k).1) := by
  by_cases h : ∃ u v, petersen.Adj u v ∧ s(u, v) = a
  · obtain ⟨u₀, v₀, hadj, rfl⟩ := h
    obtain ⟨k, hk⟩ := pedge_complete u₀ v₀ hadj
    refine ⟨k, fun u v _ huv => ?_⟩
    rcases Sym2.eq_iff.mp huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hk
    · rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
      · exact Or.inl ⟨h2, h1⟩
  · push Not at h
    exact ⟨0, fun u v hadj huv => absurd huv (h u v hadj)⟩

theorem nhf_petersen_K2_ge : (3 : ℕ∞) ≤ nhf petersen (⊤ : SimpleGraph (Fin 2)) := by
  apply le_nhf
  intro S ⟨f⟩
  by_contra hlt
  have hS : S.card ≤ 2 := by
    have : (S.card : ℕ∞) < 3 := not_le.mp hlt
    have : S.card < 3 := by exact_mod_cast this
    omega
  obtain ⟨a, b, hab⟩ := subset_pair_of_card_le_two S hS
  obtain ⟨i, hi⟩ := pedge_index a
  obtain ⟨j, hj⟩ := pedge_index b
  obtain ⟨c, havoid⟩ := pcyc_avoid i j
  apply no_odd_five (fun t => f (pcyc c t))
  intro t
  have hadj := pcyc_adj c t
  apply f.map_rel
  rw [deleteEdges_adj]
  refine ⟨hadj, fun hmem => ?_⟩
  have := hab hmem
  rw [mem_insert, mem_singleton] at this
  rcases this with h | h
  · exact (havoid t).1 (hi _ _ hadj h)
  · exact (havoid t).2 (hj _ _ hadj h)

/-- Three edges whose removal makes `P` bipartite. -/
def pDel : Finset (Sym2 (Fin 10)) := {s(0, 1), s(3, 8), s(7, 9)}

def pBip : Fin 10 → Fin 2 := ![0, 0, 1, 0, 1, 1, 1, 0, 0, 0]

theorem pBip_ok : ∀ u v : Fin 10, petersen.Adj u v →
    ¬((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (u = 3 ∧ v = 8) ∨ (u = 8 ∧ v = 3) ∨
      (u = 7 ∧ v = 9) ∨ (u = 9 ∧ v = 7)) → pBip u ≠ pBip v := by
  decide +kernel

theorem nhf_petersen_K2_le : nhf petersen (⊤ : SimpleGraph (Fin 2)) ≤ 3 := by
  have h := nhf_le_card (G := petersen) (H := (⊤ : SimpleGraph (Fin 2))) pDel ⟨{
    toFun := pBip
    map_rel' := by
      intro u v huv
      rw [deleteEdges_adj] at huv
      refine pBip_ok u v huv.1 ?_
      intro hc
      apply huv.2
      simp only [pDel, coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
        Sym2.eq_iff]
      omega }⟩
  have hc : pDel.card = 3 := by decide +kernel
  rwa [hc] at h

/-- **Observation `obs:PK2`**: `|P,K₂| = 3`. -/
theorem nhf_petersen_K2 : nhf petersen (⊤ : SimpleGraph (Fin 2)) = 3 :=
  le_antisymm nhf_petersen_K2_le nhf_petersen_K2_ge

/-! ### `γ(P,K₃) = 6` -/

def pCol : Fin 10 → Fin 3 := ![0, 1, 0, 1, 2, 1, 0, 2, 2, 1]

theorem pCol_ok : ∀ u v : Fin 10, petersen.Adj u v → pCol u ≠ pCol v := by decide +kernel

def pColHom : petersen →g (⊤ : SimpleGraph (Fin 3)) := ⟨pCol, fun h => pCol_ok _ _ h⟩

/-- `χ(P) = 3`, so `|P,K_m| = 0` for `m ≥ 3`. -/
theorem nhf_petersen_Km (m : ℕ) (hm : 3 ≤ m) : nhf petersen (⊤ : SimpleGraph (Fin m)) = 0 :=
  nhf_eq_zero_of_hom (⟨fun v => Fin.castLE hm (pCol v), fun h => by
    simpa [Fin.ext_iff] using pCol_ok _ _ h⟩)

theorem petersen_chromaticNumber : petersen.chromaticNumber = 3 := by
  apply le_antisymm
  · exact Colorable.chromaticNumber_le ⟨pColHom⟩
  · by_contra h
    have h2 : petersen.Colorable 2 := by
      rw [← chromaticNumber_le_iff_colorable]
      exact Order.le_of_lt_add_one (not_le.mp h)
    have := nhf_eq_zero_of_hom (G := petersen) h2.some
    rw [nhf_petersen_K2] at this
    exact absurd this (by decide)

theorem cls_pColHom : cls pColHom 0 = 3 ∧ cls pColHom 1 = 4 ∧ cls pColHom 2 = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- **`γ(P,K₃) = 6`** (Table `tab:Petersen`, Observation `obs:petersen_exceed`). -/
theorem gamma_petersen_K3 : gamma petersen (⊤ : SimpleGraph (Fin 3)) = 6 := by
  apply le_antisymm
  · have h2 := two_mu_eq pColHom petersen_regular
    obtain ⟨c0, c1, c2⟩ := cls_pColHom
    rw [c0, c1, c2] at h2
    norm_num at h2
    have : mu pColHom = 6 := by omega
    calc gamma petersen (⊤ : SimpleGraph (Fin 3)) ≤ mu pColHom := gamma_le_mu _
      _ = 6 := by rw [this]; rfl
  · apply le_gamma
    intro f
    have := mu_lower f (by norm_num) petersen_regular 4 (by
      intro s₁ s₂ s₃ h1 h2 h3 hs p1 p2
      simp only [Fintype.card_fin] at hs
      omega)
    exact_mod_cast (by omega : 6 ≤ mu f)

/-- The pigeonhole bound `⌈15/3⌉ = 5` is not attained: `|E(P)| = 15`. -/
theorem petersen_card_edges : petersen.edgeFinset.card = 15 := by
  have h := sum_degrees_eq_twice_card_edges petersen
  rw [sum_degree_of_regular petersen_regular, card_univ, Fintype.card_fin] at h
  omega

/-! ### `γ(P,K₅) = 2` and `γ(P,K₄) ≤ 4` (Table `tab:Petersen`) -/

def pK5 : Fin 10 → Fin 5 := ![0, 1, 0, 2, 3, 3, 2, 4, 4, 1]

theorem pK5_ok : ∀ u v : Fin 10, petersen.Adj u v → pK5 u ≠ pK5 v := by decide +kernel

def pK5Hom : petersen →g (⊤ : SimpleGraph (Fin 5)) := ⟨pK5, fun h => pK5_ok _ _ h⟩

theorem mu_pK5 : mu pK5Hom = 2 := by decide +kernel

/-- `γ(P,K₅) = 2`: the pigeonhole bound `⌈15/10⌉` is attained. -/
theorem gamma_petersen_K5 : gamma petersen (⊤ : SimpleGraph (Fin 5)) = 2 := by
  apply le_antisymm
  · calc _ ≤ (mu pK5Hom : ℕ∞) := gamma_le_mu _
      _ = 2 := by rw [mu_pK5]; rfl
  · have h := ceil_div_le_gamma (G := petersen) (H := (⊤ : SimpleGraph (Fin 5)))
      (by rw [card_edgeFinset_top_eq_card_choose_two]; decide)
    rw [petersen_card_edges, card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin] at h
    have e : (15 + Nat.choose 5 2 - 1) / Nat.choose 5 2 = 2 := by decide
    rw [e] at h
    exact_mod_cast h

def pK4 : Fin 10 → Fin 4 := ![0, 1, 0, 1, 2, 1, 2, 2, 3, 3]

theorem pK4_ok : ∀ u v : Fin 10, petersen.Adj u v → pK4 u ≠ pK4 v := by decide +kernel

def pK4Hom : petersen →g (⊤ : SimpleGraph (Fin 4)) := ⟨pK4, fun h => pK4_ok _ _ h⟩

theorem mu_pK4 : mu pK4Hom = 4 := by decide +kernel

/-- `γ(P,K₄) ≤ 4` (the matching lower bound in the paper is an exhaustive computation). -/
theorem gamma_petersen_K4_le : gamma petersen (⊤ : SimpleGraph (Fin 4)) ≤ 4 :=
  calc _ ≤ (mu pK4Hom : ℕ∞) := gamma_le_mu _
    _ = 4 := by rw [mu_pK4]; rfl

end NonHom
