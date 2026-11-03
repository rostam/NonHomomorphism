import NonHom.Turan

/-!
# The symmetric combination `m(G,H)` (Section `sec:metric`)

Proposition `prop:m_zero` (first equivalence), Theorem `thm:no_triangle`, and Table `tab:KnKm`.
The second equivalence of `prop:m_zero` (homomorphic equivalence ⇔ isomorphic cores) relies on
the theory of cores, which is not in Mathlib, and is not formalized here.
-/

open SimpleGraph

namespace NonHom

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem msym_self : msym G G = 0 := by
  simp [msym, nhf_eq_zero_of_hom (Hom.id : G →g G)]

theorem msym_comm : msym G H = msym H G := max_comm _ _

/-- Proposition `prop:m_zero`: `m(G,H) = 0` iff `G ↔ H`. -/
theorem msym_eq_zero_iff : msym G H = 0 ↔ Nonempty (G →g H) ∧ Nonempty (H →g G) := by
  simp [msym, nhf_eq_zero_iff]

/-- `K_n → K_m` for `n ≤ m`. -/
def topEmb {n m : ℕ} (h : n ≤ m) : (⊤ : SimpleGraph (Fin n)) →g (⊤ : SimpleGraph (Fin m)) :=
  ⟨Fin.castLE h, fun h' => by simpa [Fin.ext_iff] using h'⟩

/-- `m(K_n, K_m) = |K_n,K_m|` for `n ≥ m ≥ 1`. -/
theorem msym_top_top {n m : ℕ} (hm : 0 < m) (h : m ≤ n) :
    msym (⊤ : SimpleGraph (Fin n)) (⊤ : SimpleGraph (Fin m)) =
      (((n % m) * (n / m + 1).choose 2 + (m - n % m) * (n / m).choose 2 : ℕ) : ℕ∞) := by
  rw [msym, nhf_eq_zero_of_hom (topEmb h), nhf_top_top_formula n m hm]
  exact max_eq_left zero_le

/-- **Theorem `thm:no_triangle`**: `m(K₇,K₃) = 5 > 4 = m(K₇,K₅) + m(K₅,K₃)`. -/
theorem no_triangle :
    msym (⊤ : SimpleGraph (Fin 7)) (⊤ : SimpleGraph (Fin 3)) = 5 ∧
    msym (⊤ : SimpleGraph (Fin 7)) (⊤ : SimpleGraph (Fin 5)) = 2 ∧
    msym (⊤ : SimpleGraph (Fin 5)) (⊤ : SimpleGraph (Fin 3)) = 2 ∧
    msym (⊤ : SimpleGraph (Fin 5)) (⊤ : SimpleGraph (Fin 3)) +
      msym (⊤ : SimpleGraph (Fin 7)) (⊤ : SimpleGraph (Fin 5)) <
      msym (⊤ : SimpleGraph (Fin 7)) (⊤ : SimpleGraph (Fin 3)) := by
  rw [msym_top_top (by norm_num) (by norm_num), msym_top_top (by norm_num) (by norm_num),
    msym_top_top (by norm_num) (by norm_num)]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `m` is not a pseudo-metric: the triangle inequality fails. -/
theorem msym_not_triangle : ¬ ∀ (a b c : ℕ),
    msym (⊤ : SimpleGraph (Fin a)) (⊤ : SimpleGraph (Fin c)) ≤
      msym (⊤ : SimpleGraph (Fin a)) (⊤ : SimpleGraph (Fin b)) +
      msym (⊤ : SimpleGraph (Fin b)) (⊤ : SimpleGraph (Fin c)) := by
  intro h
  have := h 7 5 3
  obtain ⟨_, _, _, hlt⟩ := no_triangle
  rw [add_comm] at this
  exact absurd this (not_le.mpr hlt)

/-- Table `tab:KnKm`: `|K_n, K_m|` for `n = 2..7`, `m = 2..6`. -/
theorem table_KnKm :
    (List.range 6).map (fun i => (List.range 5).map (fun j =>
      let n := i + 2; let m := j + 2
      (n % m) * (n / m + 1).choose 2 + (m - n % m) * (n / m).choose 2)) =
      [[0,0,0,0,0],[1,0,0,0,0],[2,1,0,0,0],[4,2,1,0,0],[6,3,2,1,0],[9,5,3,2,1]] := by
  decide

end NonHom
