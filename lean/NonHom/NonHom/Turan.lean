import NonHom.NHF

/-!
# Complete graphs and Turán's theorem

Theorem `thm:KnKm`: `|K_n,K_m| = C(n,2) - t(n,m)` with the explicit formula
`r·C(q+1,2) + (m-r)·C(q,2)` for `n = qm + r`, and `|K_{n+1},K_n| = 1`.
Theorem `thm:lower_bound`: `|G,H| ≥ |E(G)| - t(|V(G)|, χ(H))`.
-/

open SimpleGraph Finset

namespace NonHom

variable {V W : Type*}

section lowerBound

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W}

/-- If `H` is `c`-colourable then any `G - S` mapping to `H` is `c`-colourable, hence
`K_{c+1}`-free, hence has at most `t(|V|, c)` edges; so `|S| ≥ |E(G)| - t(|V|,c)`. -/
theorem card_sub_turanNumber_le_nhf (c : ℕ) (hc : H.Colorable c) :
    ((G.edgeFinset.card - turanNumber (Fintype.card V) c : ℕ) : ℕ∞) ≤ nhf G H := by
  apply le_nhf
  intro S ⟨f⟩
  norm_cast
  have hcol : (G.deleteEdges ↑S).Colorable c := Colorable.of_hom f hc
  have hcf : (G.deleteEdges ↑S).CliqueFree (c + 1) := hcol.cliqueFree (Nat.lt_succ_self c)
  have hle := hcf.card_edgeFinset_le
  have hE : (G.deleteEdges ↑S).edgeFinset = G.edgeFinset \ S := edgeFinset_deleteEdges S
  rw [hE] at hle
  have := card_le_card_sdiff_add_card (s := G.edgeFinset) (t := S)
  omega

/-- Theorem `thm:lower_bound`: `|G,H| ≥ |E(G)| - t(|V(G)|, χ(H))` for finite `H`. -/
theorem lower_bound [Fintype W] :
    ((G.edgeFinset.card - turanNumber (Fintype.card V) H.chromaticNumber.toNat : ℕ) : ℕ∞)
      ≤ nhf G H :=
  card_sub_turanNumber_le_nhf _ (colorable_chromaticNumber_of_fintype H)

end lowerBound

section complete

/-- The Turán graph is `m`-colourable (colour `v` by `v % m`). -/
def turanGraphColoring (n m : ℕ) (hm : 0 < m) : (turanGraph n m).Coloring (Fin m) :=
  Coloring.mk (fun v => ⟨v.val % m, Nat.mod_lt _ hm⟩) fun {v w} h => by
    rw [turanGraph_adj] at h
    intro heq
    apply h
    simpa [Fin.ext_iff] using heq

theorem turanGraph_colorable (n m : ℕ) (hm : 0 < m) : (turanGraph n m).Colorable m :=
  ⟨turanGraphColoring n m hm⟩

theorem top_colorable_fin (m : ℕ) : (⊤ : SimpleGraph (Fin m)).Colorable m := by
  simpa using colorable_of_fintype (⊤ : SimpleGraph (Fin m))

/-- Theorem `thm:KnKm`: `|K_n,K_m| = C(n,2) - t(n,m)` for `m ≥ 1`. -/
theorem nhf_top_top (n m : ℕ) (hm : 0 < m) :
    nhf (⊤ : SimpleGraph (Fin n)) (⊤ : SimpleGraph (Fin m)) =
      ((n.choose 2 - turanNumber n m : ℕ) : ℕ∞) := by
  apply le_antisymm
  · -- delete the edges outside the Turán graph
    let S : Finset (Sym2 (Fin n)) := (⊤ : SimpleGraph (Fin n)).edgeFinset \ (turanGraph n m).edgeFinset
    have hdel : (⊤ : SimpleGraph (Fin n)).deleteEdges ↑S = turanGraph n m := by
      have h := deleteEdges_sdiff_eq_of_le (G := (⊤ : SimpleGraph (Fin n))) (H := turanGraph n m) le_top
      simpa [S, coe_sdiff, coe_edgeFinset] using h
    have hhom : Nonempty ((⊤ : SimpleGraph (Fin n)).deleteEdges ↑S →g (⊤ : SimpleGraph (Fin m))) := by
      rw [hdel]
      exact ⟨turanGraphColoring n m hm⟩
    refine (nhf_le_card S hhom).trans ?_
    norm_cast
    rw [card_sdiff_of_subset (edgeFinset_mono le_top), card_edgeFinset_top_eq_card_choose_two,
      Fintype.card_fin]
  · have := card_sub_turanNumber_le_nhf (G := (⊤ : SimpleGraph (Fin n)))
      (H := (⊤ : SimpleGraph (Fin m))) m (top_colorable_fin m)
    rwa [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin] at this

/-- `t(n,m) = C(n,2)` when `n ≤ m`. -/
theorem turanNumber_of_le {n m : ℕ} (h : n ≤ m) : turanNumber n m = n.choose 2 := by
  have htop : turanGraph n m = ⊤ := turanGraph_eq_top.mpr (Or.inr h)
  have he : (turanGraph n m).edgeFinset = (⊤ : SimpleGraph (Fin n)).edgeFinset := by
    ext e; simp only [mem_edgeFinset, htop]
  rw [turanNumber, he, card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]

theorem choose_two_succ (k : ℕ) : (k + 1).choose 2 = k.choose 2 + k := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]

theorem choose_two_add (a b : ℕ) : (a + b).choose 2 = a.choose 2 + a * b + b.choose 2 := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, choose_two_succ, ih, choose_two_succ]
    ring

/-- The explicit formula in Theorem `thm:KnKm`: for `n = q·m + r` with `r < m`
(written `m = r + s + 1`), `C(n,2) - t(n,m) = r·C(q+1,2) + (m-r)·C(q,2)`. Stated additively. -/
theorem turanNumber_add_formula (q r s : ℕ) :
    turanNumber (q * (r + s + 1) + r) (r + s + 1) + (r * (q + 1).choose 2 + (s + 1) * q.choose 2) =
      (q * (r + s + 1) + r).choose 2 := by
  induction q with
  | zero =>
    simp [turanNumber_of_le (show r ≤ r + s + 1 by omega)]
  | succ q ih =>
    have h1 : (q + 1) * (r + s + 1) + r = (q * (r + s + 1) + r) + (r + s + 1) := by ring
    rw [h1, turanNumber_add, Nat.add_sub_cancel, choose_two_add (q * (r + s + 1) + r),
      choose_two_succ (q + 1), choose_two_succ q]
    rw [choose_two_succ q] at ih
    zify at ih ⊢
    linear_combination ih

/-- Theorem `thm:KnKm`, explicit form: for `m ≥ 1`, writing `q = n / m`, `r = n % m`,
`|K_n,K_m| = r·C(q+1,2) + (m-r)·C(q,2)`. -/
theorem nhf_top_top_formula (n m : ℕ) (hm : 0 < m) :
    nhf (⊤ : SimpleGraph (Fin n)) (⊤ : SimpleGraph (Fin m)) =
      (((n % m) * (n / m + 1).choose 2 + (m - n % m) * (n / m).choose 2 : ℕ) : ℕ∞) := by
  rw [nhf_top_top n m hm]
  congr 1
  obtain ⟨s, hs⟩ : ∃ s, m = n % m + s + 1 := ⟨m - n % m - 1, by have := Nat.mod_lt n hm; omega⟩
  have key := turanNumber_add_formula (n / m) (n % m) s
  rw [← hs, Nat.div_add_mod' n m] at key
  have : m - n % m = s + 1 := by omega
  rw [this]
  omega

/-- Theorem `thm:KnKm`, last clause: `|K_{n+1},K_n| = 1` for `n ≥ 1`. -/
theorem nhf_top_succ_top (n : ℕ) (hn : 0 < n) :
    nhf (⊤ : SimpleGraph (Fin (n + 1))) (⊤ : SimpleGraph (Fin n)) = 1 := by
  rw [nhf_top_top (n + 1) n hn]
  have h1 := turanNumber_add (n := 1) (r := n)
  rw [Nat.add_comm 1 n, turanNumber_of_le hn] at h1
  have h2 := choose_two_succ n
  have h3 : (Nat.succ 0).choose 2 = 0 := rfl
  have : (n + 1).choose 2 - turanNumber (n + 1) n = 1 := by omega
  rw [this]
  rfl

end complete

end NonHom
