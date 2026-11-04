import NonHom.Families

/-!
# Joins with an independent set

For a graph `G₁` with at least one edge and `k ≥ 1`, let `J = G₁ + \bar K_k` (every vertex of `G₁`
joined to every one of `k` new independent vertices). Then

  `γ(J, K₃) = max(|E(G₁)|, k·β(G₁))`,

where `β(G₁)` is the least possible size of the larger class of a proper 2-colouring of `G₁`
(`∞` if `G₁` is not bipartite). This contains the book, wheel, friendship and `K_{p,q,r}`
formulas as special cases.
-/

open SimpleGraph Finset

namespace NonHom

local notation "K3" => (⊤ : SimpleGraph (Fin 3))

variable {V : Type*} [Fintype V] [DecidableEq V] (G₁ : SimpleGraph V) [DecidableRel G₁.Adj] (k : ℕ)

def joinAdj : V ⊕ Fin k → V ⊕ Fin k → Prop
  | .inl a, .inl b => G₁.Adj a b
  | .inl _, .inr _ => True
  | .inr _, .inl _ => True
  | .inr _, .inr _ => False

instance : DecidableRel (joinAdj G₁ k) := fun u v => by
  cases u <;> cases v <;> unfold joinAdj <;> infer_instance

/-- `G₁ + \bar K_k`. -/
def joinInd : SimpleGraph (V ⊕ Fin k) where
  Adj := joinAdj G₁ k
  symm := ⟨by
    rintro (a | a) (b | b) h <;> simp only [joinAdj] at h ⊢ <;>
      first | exact h.symm | trivial | exact h.elim⟩
  loopless := ⟨by rintro (a | a) h <;> simp [joinAdj] at h⟩

instance : DecidableRel (joinInd G₁ k).Adj := inferInstanceAs (DecidableRel (joinAdj G₁ k))

/-- `β(G₁)`: least larger class over proper 2-colourings. -/
noncomputable def beta : ℕ∞ :=
  ⨅ g : G₁ →g (⊤ : SimpleGraph (Fin 2)),
    (max (univ.filter fun v => g v = 0).card (univ.filter fun v => g v = 1).card : ℕ∞)

variable {G₁ k}

theorem enat_cast_max (a b : ℕ) : ((max a b : ℕ) : ℕ∞) = max (a : ℕ∞) b := Nat.mono_cast.map_max

theorem two_others : ∀ c : Fin 3, ∃ a b : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    ∀ z : Fin 3, z = a ∨ z = b ∨ z = c := by decide

theorem K3_edges_of (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ x y : Fin 3, x ≠ y → s(x, y) = s(a, b) ∨ s(x, y) = s(a, c) ∨ s(x, y) = s(b, c) := by
  revert a b c; decide

theorem pair_of_two (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ x y : Fin 3, x ≠ y → x ≠ c → y ≠ c → s(x, y) = s(a, b) := by
  revert a b c; decide

/-- Structure of loads when all independent vertices get colour `c`. -/
theorem mu_join (f : joinInd G₁ k →g K3) (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hall : ∀ z : Fin 3, z = a ∨ z = b ∨ z = c) (hc : ∀ j, f (.inr j) = c) (hk : 0 < k) :
    mu f = max G₁.edgeFinset.card
      (max (k * (univ.filter fun v => f (.inl v) = a).card)
        (k * (univ.filter fun v => f (.inl v) = b).card)) := by
  classical
  have hnc : ∀ v, f (.inl v) ≠ c := fun v h =>
    f.map_rel (show (joinInd G₁ k).Adj (.inl v) (.inr ⟨0, hk⟩) from trivial) (h.trans (hc _).symm)
  -- the load of `s(x, c)` for `x ≠ c` is `k·#{v : f v = x}`
  have Lxc : ∀ x, x ≠ c → load f s(x, c) = k * (univ.filter fun v => f (.inl v) = x).card := by
    intro x hx
    have hprod : k * (univ.filter fun v => f (.inl v) = x).card =
        ((univ.filter fun v => f (.inl v) = x) ×ˢ (univ : Finset (Fin k))).card := by
      rw [card_product, card_univ, Fintype.card_fin, mul_comm]
    rw [load_eq_card_darts f hx, hprod]
    symm
    apply card_bij (fun p _ => (⟨(.inl p.1, .inr p.2), trivial⟩ : (joinInd G₁ k).Dart))
    · intro p hp
      simp only [mem_product, mem_filter, mem_univ, true_and, and_true] at hp
      exact mem_filter.mpr ⟨mem_univ _, hp, hc _⟩
    · intro p _ q _ h
      have h' := congrArg (fun d : (joinInd G₁ k).Dart => d.toProd) h
      simp only [Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] at h'
      exact Prod.ext h'.1 h'.2
    · intro d hd
      simp only [mem_filter, mem_univ, true_and] at hd
      obtain ⟨⟨u, w⟩, hadj⟩ := d
      simp only at hd
      rcases u with u | u
      · rcases w with w | w
        · exact absurd hd.2 (hnc w)
        · exact ⟨(u, w), by simp [hd.1], rfl⟩
      · exact absurd ((hc u).symm.trans hd.1) (Ne.symm hx)
  -- the load of `s(a, b)` is `|E(G₁)|`
  have Lab : load f s(a, b) = G₁.edgeFinset.card := by
    unfold load
    symm
    apply card_bij (fun e _ => e.map Sum.inl)
    · intro e he
      rw [mem_edgeFinset] at he
      simp only [mem_filter, mem_edgeFinset]
      induction e using Sym2.ind with
      | _ u v =>
        refine ⟨he, ?_⟩
        simp only [Sym2.map_mk]
        have hne : f (.inl u) ≠ f (.inl v) := f.map_rel he
        exact pair_of_two a b c hab hac hbc _ _ hne (hnc u) (hnc v)
    · intro e₁ _ e₂ _ h
      exact Sym2.map.injective Sum.inl_injective h
    · intro e he
      simp only [mem_filter, mem_edgeFinset] at he
      obtain ⟨he, hmap⟩ := he
      induction e using Sym2.ind with
      | _ p q =>
        rcases p with u | u <;> rcases q with w | w
        · exact ⟨s(u, w), mem_edgeFinset.mpr he, rfl⟩
        · exfalso
          rw [Sym2.map_mk, hc] at hmap
          rcases Sym2.eq_iff.mp hmap with ⟨_, h⟩ | ⟨_, h⟩
          · exact hbc h.symm
          · exact hac h.symm
        · exfalso
          rw [Sym2.map_mk, hc] at hmap
          rcases Sym2.eq_iff.mp hmap with ⟨h, _⟩ | ⟨h, _⟩
          · exact hac h.symm
          · exact hbc h.symm
        · exact absurd he (by simp [joinInd, joinAdj])
  apply le_antisymm
  · apply Finset.sup_le
    intro e he
    rw [mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ p q =>
      have hne : f p ≠ f q := f.map_rel he
      rw [Sym2.map_mk]
      rcases K3_edges_of a b c hab hac hbc _ _ hne with h | h | h <;> rw [h]
      · rw [Lab]; exact le_max_left _ _
      · rw [Lxc a hac]; exact (le_max_left _ _).trans (le_max_right _ _)
      · rw [Lxc b hbc]; exact (le_max_right _ _).trans (le_max_right _ _)
  · refine max_le ?_ (max_le ?_ ?_)
    · rw [← Lab]; exact load_le_mu f _
    · rw [← Lxc a hac]; exact load_le_mu f _
    · rw [← Lxc b hbc]; exact load_le_mu f _

/-- **Join theorem.** If `G₁` has an edge and `k ≥ 1`,
`γ(G₁ + \bar K_k, K₃) = max(|E(G₁)|, k·β(G₁))`. -/
theorem gamma_join (hk : 0 < k) (hG : G₁.edgeSet.Nonempty) :
    gamma (joinInd G₁ k) K3 = max (G₁.edgeFinset.card : ℕ∞) (k * beta G₁) := by
  classical
  apply le_antisymm
  · -- upper bound from an optimal 2-colouring
    by_cases hbip : Nonempty (G₁ →g (⊤ : SimpleGraph (Fin 2)))
    · have hne : (Set.range fun g : G₁ →g (⊤ : SimpleGraph (Fin 2)) =>
          (max (univ.filter fun v => g v = 0).card (univ.filter fun v => g v = 1).card : ℕ∞)).Nonempty :=
        Set.range_nonempty _
      obtain ⟨g, hg⟩ := csInf_mem hne
      let f : joinInd G₁ k →g K3 := ⟨Sum.elim (fun v => Fin.castSucc (g v)) (fun _ => 2), by
        rintro (u | u) (w | w) h
        · exact fun heq => g.map_rel h (Fin.castSucc_injective _ heq)
        · show Fin.castSucc (g u) ≠ 2
          exact (Fin.castSucc_lt_last (g u)).ne
        · show (2 : Fin 3) ≠ Fin.castSucc (g w)
          exact (Fin.castSucc_lt_last (g w)).ne'
        · exact absurd h (by simp [joinInd, joinAdj])⟩
      have hmu := mu_join f 0 1 2 (by decide) (by decide) (by decide) (by decide) (fun _ => rfl) hk
      have e0 : (univ.filter fun v => f (.inl v) = 0) = univ.filter fun v => g v = 0 := by
        ext v; simp only [mem_filter, mem_univ, true_and]
        change Fin.castSucc (g v) = 0 ↔ g v = 0
        rw [Fin.ext_iff, Fin.ext_iff, Fin.coe_castSucc]; rfl
      have e1 : (univ.filter fun v => f (.inl v) = 1) = univ.filter fun v => g v = 1 := by
        ext v; simp only [mem_filter, mem_univ, true_and]
        change Fin.castSucc (g v) = 1 ↔ g v = 1
        rw [Fin.ext_iff, Fin.ext_iff, Fin.coe_castSucc]; rfl
      rw [e0, e1] at hmu
      calc gamma (joinInd G₁ k) K3 ≤ mu f := gamma_le_mu f
        _ = _ := by
          have hg' : (⨅ g : G₁ →g (⊤ : SimpleGraph (Fin 2)), (max (univ.filter fun v => g v = 0).card
              (univ.filter fun v => g v = 1).card : ℕ∞)) =
              (max (univ.filter fun v => g v = 0).card (univ.filter fun v => g v = 1).card : ℕ∞) :=
            hg.symm
          rw [hmu, beta, hg']
          simp only [enat_cast_max, Nat.cast_mul]
          rw [mul_max_of_nonneg _ _ bot_le]
    · rw [not_nonempty_iff] at hbip
      have : beta G₁ = ⊤ := by simp [beta, iInf_of_empty]
      rw [this, ENat.mul_top (by exact_mod_cast hk.ne'), max_eq_right le_top]
      exact le_top
  · apply le_gamma
    intro f
    set c := f (.inr ⟨0, hk⟩)
    obtain ⟨a, b, hab, hac, hbc, hall⟩ := two_others c
    have hnc : ∀ v, f (.inl v) ≠ c := fun v h =>
      f.map_rel (show (joinInd G₁ k).Adj (.inl v) (.inr ⟨0, hk⟩) from trivial) h
    -- every independent vertex has colour `c`
    have hcall : ∀ j, f (.inr j) = c := by
      intro j
      by_contra hj
      obtain ⟨e, he⟩ := hG
      induction e using Sym2.ind with
      | _ u w =>
        have h1 : f (.inl u) ≠ f (.inl w) := f.map_rel he
        have hu : f (.inl u) ≠ f (.inr j) :=
          f.map_rel (show (joinInd G₁ k).Adj (.inl u) (.inr j) from trivial)
        have hw : f (.inl w) ≠ f (.inr j) :=
          f.map_rel (show (joinInd G₁ k).Adj (.inl w) (.inr j) from trivial)
        exact four_colors (f (.inr j)) c (f (.inl u)) (f (.inl w)) hj hu (hnc u) hw (hnc w) h1.symm
    have hmu := mu_join f a b c hab hac hbc hall hcall hk
    -- the restriction to `G₁` is a 2-colouring
    let g : G₁ →g (⊤ : SimpleGraph (Fin 2)) := ⟨fun v => if f (.inl v) = a then 0 else 1, by
      intro u w h
      have h1 : f (.inl u) ≠ f (.inl w) := f.map_rel h
      have hu := hnc u
      have hw := hnc w
      simp only [top_adj, ne_eq]
      split_ifs with h2 h3 h3 <;> simp_all
      · rcases hall (f (.inl u)) with h | h | h <;> rcases hall (f (.inl w)) with h' | h' | h' <;>
          simp_all⟩
    have e0 : (univ.filter fun v => g v = 0) = univ.filter fun v => f (.inl v) = a := by
      ext v; simp only [mem_filter, mem_univ, true_and]
      change (if f (.inl v) = a then (0 : Fin 2) else 1) = 0 ↔ f (.inl v) = a
      split_ifs <;> simp_all
    have e1 : (univ.filter fun v => g v = 1) = univ.filter fun v => f (.inl v) = b := by
      ext v; simp only [mem_filter, mem_univ, true_and]
      change (if f (.inl v) = a then (0 : Fin 2) else 1) = 1 ↔ f (.inl v) = b
      constructor
      · intro h; split_ifs at h with h'
        · simp at h
        · rcases hall (f (.inl v)) with h'' | h'' | h''
          · exact absurd h'' h'
          · exact h''
          · exact absurd h'' (hnc v)
      · intro h; rw [if_neg (by rw [h]; exact Ne.symm hab)]
    have hb : beta G₁ ≤ max ((univ.filter fun v => f (.inl v) = a).card : ℕ∞)
        (univ.filter fun v => f (.inl v) = b).card := by
      rw [← e0, ← e1]
      exact iInf_le (fun g : G₁ →g (⊤ : SimpleGraph (Fin 2)) =>
        (max (univ.filter fun v => g v = 0).card (univ.filter fun v => g v = 1).card : ℕ∞)) g
    rw [hmu]
    simp only [enat_cast_max, Nat.cast_mul]
    refine max_le_max le_rfl ?_
    rw [← mul_max_of_nonneg _ _ bot_le]
    exact mul_le_mul_right hb _

end NonHom
