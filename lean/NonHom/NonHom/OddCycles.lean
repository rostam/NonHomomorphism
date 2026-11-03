import NonHom.Cycles

/-!
# Homomorphisms between cycles (Observation `obs:CnC5_pattern`, Tables `tab:CnC5`, `tab:CnC7`)

* For odd `m ≥ 3`: `C_n → C_m` iff `n` is even or `n ≥ m`.
* Exact values `γ(C₆,C₅) = 2`, `γ(C₈,C₇) = γ(C₁₀,C₇) = γ(C₁₂,C₇) = 2`, `γ(C₁₅,C₇) = 3`.
  Each equals the pigeonhole bound `⌈n/m⌉`, which contradicts the observation text (for `C₆`)
  and the "achieves bound?" column of Table `tab:CnC7` (for `C₈, C₁₀, C₁₂, C₁₅`).
-/

open SimpleGraph Finset

namespace NonHom

theorem fin_sub_val {n : ℕ} (a b : Fin n) :
    (a - b).val = if b.val ≤ a.val then a.val - b.val else n + a.val - b.val := by
  split_ifs with h
  · exact Fin.coe_sub_iff_le.mpr h
  · exact Fin.coe_sub_iff_lt.mpr (Nat.lt_of_not_le h)

theorem cycle_adj_of_val {k : ℕ} {u v : Fin (k + 3)}
    (h : u.val = v.val + 1 ∨ v.val = u.val + 1 ∨ (u.val = 0 ∧ v.val = k + 2) ∨
      (v.val = 0 ∧ u.val = k + 2)) : (cycleGraph (k + 3)).Adj u v := by
  rw [cycleGraph_adj', fin_sub_val, fin_sub_val]
  have hu := u.isLt
  have hv := v.isLt
  split_ifs <;> omega

/-- `C_n → C_m` for even `n` and `m ≥ 2` (through an edge). -/
theorem hom_cycle_of_even (n m : ℕ) (hn : Even n) (hm : 2 ≤ m) :
    Nonempty (cycleGraph n →g cycleGraph m) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  refine ⟨⟨fun i => if cycleGraph.bicoloring_of_even n hn i then 0 else 1, ?_⟩⟩
  intro u v huv
  have hne := (cycleGraph.bicoloring_of_even n hn).valid huv
  revert hne
  cases cycleGraph.bicoloring_of_even n hn u <;> cases cycleGraph.bicoloring_of_even n hn v <;>
    simp [cycleGraph_adj]

/-- `C_n → C_m` for odd `3 ≤ m ≤ n` with `n - m` even: wind once, then oscillate. -/
theorem hom_cycle_of_ge (n m : ℕ) (hm : 3 ≤ m) (hmn : m ≤ n) (hpar : Even (n - m)) :
    Nonempty (cycleGraph n →g cycleGraph m) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l, m = l + 3 := ⟨m - 3, by omega⟩
  obtain ⟨t, ht⟩ := hpar
  refine ⟨⟨fun i => ⟨if i.val < l + 3 then i.val else if (i.val - (l + 3)) % 2 = 0 then l + 1 else l + 2,
    by split_ifs <;> omega⟩, ?_⟩⟩
  intro u v huv
  have h := cycle_adj_val huv
  apply cycle_adj_of_val
  simp only
  split_ifs <;> omega

/-- `C_n ↛ C_m` for odd `n < m`: the image misses a vertex, and `C_m` minus a vertex is a path. -/
theorem no_hom_cycle_of_odd_lt (n m : ℕ) (hn3 : 3 ≤ n) (hodd : Odd n) (hnm : n < m) :
    IsEmpty (cycleGraph n →g cycleGraph m) := by
  refine ⟨fun g => ?_⟩
  obtain ⟨l, rfl⟩ : ∃ l, m = l + 3 := ⟨m - 3, by omega⟩
  have hns : ¬ Function.Surjective g := fun hs => by
    have := Fintype.card_le_of_surjective g hs
    simp at this; omega
  simp only [Function.Surjective, not_forall, not_exists] at hns
  obtain ⟨w, hw⟩ := hns
  -- position along the path `C_m - w`
  let p : Fin (l + 3) → ℕ := fun x =>
    if w.val < x.val then x.val - w.val - 1 else x.val + (l + 3) - w.val - 1
  have hp : ∀ x y : Fin (l + 3), x ≠ w → y ≠ w → (cycleGraph (l + 3)).Adj x y →
      p x % 2 ≠ p y % 2 := by
    intro x y hx hy hxy
    have h := cycle_adj_val hxy
    have hx' : x.val ≠ w.val := fun e => hx (Fin.ext e)
    have hy' : y.val ≠ w.val := fun e => hy (Fin.ext e)
    have := w.isLt
    simp only [p]
    split_ifs <;> omega
  have hcol : (cycleGraph n).Colorable 2 := ⟨Coloring.mk (fun i => ⟨p (g i) % 2, Nat.mod_lt _ (by norm_num)⟩)
    (by
      intro u v huv
      have := hp (g u) (g v) (hw u) (hw v) (g.map_rel huv)
      simpa [Fin.ext_iff] using this)⟩
  have h3 := chromaticNumber_cycleGraph_of_odd n (by omega) hodd
  have := hcol.chromaticNumber_le
  rw [h3] at this
  exact absurd this (by decide)

/-- **Observation `obs:CnC5_pattern`** (general form): for odd `m ≥ 3` and `n ≥ 3`,
`C_n → C_m` iff `n` is even or `n ≥ m`. -/
theorem cycle_hom_iff (n m : ℕ) (hn : 3 ≤ n) (hm : 3 ≤ m) (hmo : Odd m) :
    Nonempty (cycleGraph n →g cycleGraph m) ↔ Even n ∨ m ≤ n := by
  constructor
  · intro ⟨g⟩
    by_contra h
    push Not at h
    obtain ⟨hne, hlt⟩ := h
    exact (no_hom_cycle_of_odd_lt n m hn (Nat.not_even_iff_odd.mp hne) hlt).false g
  · rintro (he | hle)
    · exact hom_cycle_of_even n m he (by omega)
    · by_cases he : Even n
      · exact hom_cycle_of_even n m he (by omega)
      · exact hom_cycle_of_ge n m hm hle
          (by rw [Nat.not_even_iff_odd] at he; exact Nat.Odd.sub_odd he hmo)

/-! ### Small exact values -/

theorem card_edges_cycle (k : ℕ) : (cycleGraph (k + 3)).edgeFinset.card = k + 3 := by
  have h := sum_degrees_eq_twice_card_edges (cycleGraph (k + 3))
  rw [sum_degree_of_regular (cycleGraph_regular k), card_univ, Fintype.card_fin] at h
  omega

/-- The pigeonhole bound `⌈n/m⌉ ≤ γ(C_n, C_m)`. -/
theorem pigeon_cycle (k l : ℕ) :
    ((((k + 3) + (l + 3) - 1) / (l + 3) : ℕ) : ℕ∞) ≤ gamma (cycleGraph (k + 3)) (cycleGraph (l + 3)) := by
  have := ceil_div_le_gamma (G := cycleGraph (k + 3)) (H := cycleGraph (l + 3))
    (by rw [card_edges_cycle]; omega)
  rwa [card_edges_cycle, card_edges_cycle] at this

/-- A homomorphism given by a list of images (checked by `decide`). -/
def cycHom (n m : ℕ) (f : Fin n → Fin m)
    (hf : ∀ u v : Fin n, (cycleGraph n).Adj u v → (cycleGraph m).Adj (f u) (f v)) :
    cycleGraph n →g cycleGraph m := ⟨f, fun h => hf _ _ h⟩

def map_C6_C5 : Fin 6 → Fin 5 := ![0, 1, 2, 3, 2, 1]

theorem map_C6_C5_hom : ∀ u v : Fin 6, (cycleGraph 6).Adj u v →
    (cycleGraph 5).Adj (map_C6_C5 u) (map_C6_C5 v) := by decide +kernel

theorem mu_C6_C5 : mu (cycHom 6 5 map_C6_C5 map_C6_C5_hom) = 2 := by decide +kernel

theorem gamma_C6_C5 : gamma (cycleGraph 6) (cycleGraph 5) = 2 := by
  apply le_antisymm
  · calc _ ≤ (mu (cycHom 6 5 map_C6_C5 map_C6_C5_hom) : ℕ∞) := gamma_le_mu _
      _ = 2 := by rw [mu_C6_C5]; rfl
  · simpa using pigeon_cycle 3 2

def map_C8_C7 : Fin 8 → Fin 7 := ![0, 1, 2, 3, 4, 3, 2, 1]

theorem map_C8_C7_hom : ∀ u v : Fin 8, (cycleGraph 8).Adj u v →
    (cycleGraph 7).Adj (map_C8_C7 u) (map_C8_C7 v) := by decide +kernel

theorem mu_C8_C7 : mu (cycHom 8 7 map_C8_C7 map_C8_C7_hom) = 2 := by decide +kernel

theorem gamma_C8_C7 : gamma (cycleGraph 8) (cycleGraph 7) = 2 := by
  apply le_antisymm
  · calc _ ≤ (mu (cycHom 8 7 map_C8_C7 map_C8_C7_hom) : ℕ∞) := gamma_le_mu _
      _ = 2 := by rw [mu_C8_C7]; rfl
  · simpa using pigeon_cycle 5 4

def map_C10_C7 : Fin 10 → Fin 7 := ![0, 1, 2, 3, 4, 5, 4, 3, 2, 1]

theorem map_C10_C7_hom : ∀ u v : Fin 10, (cycleGraph 10).Adj u v →
    (cycleGraph 7).Adj (map_C10_C7 u) (map_C10_C7 v) := by decide +kernel

theorem mu_C10_C7 : mu (cycHom 10 7 map_C10_C7 map_C10_C7_hom) = 2 := by decide +kernel

theorem gamma_C10_C7 : gamma (cycleGraph 10) (cycleGraph 7) = 2 := by
  apply le_antisymm
  · calc _ ≤ (mu (cycHom 10 7 map_C10_C7 map_C10_C7_hom) : ℕ∞) := gamma_le_mu _
      _ = 2 := by rw [mu_C10_C7]; rfl
  · simpa using pigeon_cycle 7 4

def map_C12_C7 : Fin 12 → Fin 7 := ![0, 1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1]

theorem map_C12_C7_hom : ∀ u v : Fin 12, (cycleGraph 12).Adj u v →
    (cycleGraph 7).Adj (map_C12_C7 u) (map_C12_C7 v) := by decide +kernel

theorem mu_C12_C7 : mu (cycHom 12 7 map_C12_C7 map_C12_C7_hom) = 2 := by decide +kernel

theorem gamma_C12_C7 : gamma (cycleGraph 12) (cycleGraph 7) = 2 := by
  apply le_antisymm
  · calc _ ≤ (mu (cycHom 12 7 map_C12_C7 map_C12_C7_hom) : ℕ∞) := gamma_le_mu _
      _ = 2 := by rw [mu_C12_C7]; rfl
  · simpa using pigeon_cycle 9 4

def map_C15_C7 : Fin 15 → Fin 7 := ![0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 1, 0, 6, 5, 6]

theorem map_C15_C7_hom : ∀ u v : Fin 15, (cycleGraph 15).Adj u v →
    (cycleGraph 7).Adj (map_C15_C7 u) (map_C15_C7 v) := by decide +kernel

theorem mu_C15_C7 : mu (cycHom 15 7 map_C15_C7 map_C15_C7_hom) = 3 := by decide +kernel

theorem gamma_C15_C7 : gamma (cycleGraph 15) (cycleGraph 7) = 3 := by
  apply le_antisymm
  · calc _ ≤ (mu (cycHom 15 7 map_C15_C7 map_C15_C7_hom) : ℕ∞) := gamma_le_mu _
      _ = 3 := by rw [mu_C15_C7]; rfl
  · simpa using pigeon_cycle 12 4

end NonHom
