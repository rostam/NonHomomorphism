import NonHom.OpenProblems

/-!
# Squared cycles (`open_problems/sage_a1_5/README.md`, section 3)

The README proves the lower bound `|C_n², C_{2k+1}| ≥ ⌈n/2⌉`: kept graphs are triangle-free and
each edge lies in at most two of the `n` triangles `{i, i+1, i+2}`. We formalize it for every
triangle-free target `H` and `n ≥ 5`. (The exact values in that section are conjectures.)
-/

open SimpleGraph Finset

namespace NonHom

variable (n : ℕ)

/-- `i + c` on `ℤ_n`, as a vertex. -/
def vtx (hn : 5 ≤ n) (i : Fin n) (c : ℕ) : Fin n := ⟨(i.val + c) % n, Nat.mod_lt _ (by omega)⟩

theorem vtx_val (hn : 5 ≤ n) (i : Fin n) (c : ℕ) (hc : c ≤ 2) :
    (vtx n hn i c).val = if i.val + c < n then i.val + c else i.val + c - n := by
  simp only [vtx]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by have := i.isLt; omega)]

/-- `v = u + 1` or `v = u + 2` in `ℤ_n`, written on values. -/
def D (u v : Fin n) : Prop :=
  v.val = u.val + 1 ∨ v.val = u.val + 2 ∨ v.val + n = u.val + 1 ∨ v.val + n = u.val + 2

/-- `C_n²`: the circulant graph with jumps `1, 2`. -/
def sqCycle : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (D n u v ∨ D n v u)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The three edges of the triangle `{i, i+1, i+2}`. -/
def triEdge (hn : 5 ≤ n) (i : Fin n) : Fin 3 → Sym2 (Fin n) :=
  ![s(vtx n hn i 0, vtx n hn i 1), s(vtx n hn i 1, vtx n hn i 2), s(vtx n hn i 0, vtx n hn i 2)]

/-- The three vertices of triangle `i` are pairwise adjacent. -/
theorem tri_adj (hn : 5 ≤ n) (i : Fin n) :
    (sqCycle n).Adj (vtx n hn i 0) (vtx n hn i 1) ∧ (sqCycle n).Adj (vtx n hn i 0) (vtx n hn i 2) ∧
      (sqCycle n).Adj (vtx n hn i 1) (vtx n hn i 2) := by
  have hi := i.isLt
  have h0 := vtx_val n hn i 0 (by norm_num)
  have h1 := vtx_val n hn i 1 (by norm_num)
  have h2 := vtx_val n hn i 2 (by norm_num)
  simp only [sqCycle, D, ne_eq, Fin.ext_iff]
  rw [h0, h1, h2]
  split_ifs <;> omega

theorem pair_rel (hn : 5 ≤ n) (i j : Fin n) (t t' : Fin 3)
    (h : triEdge n hn i t = triEdge n hn j t') :
    i.val = j.val ∨ j.val = i.val + 1 ∨ i.val = j.val + 1 ∨ (i.val + 1 = n ∧ j.val = 0) ∨
      (j.val + 1 = n ∧ i.val = 0) := by
  have hi := i.isLt
  have hj := j.isLt
  have a0 := vtx_val n hn i 0 (by norm_num)
  have a1 := vtx_val n hn i 1 (by norm_num)
  have a2 := vtx_val n hn i 2 (by norm_num)
  have b0 := vtx_val n hn j 0 (by norm_num)
  have b1 := vtx_val n hn j 1 (by norm_num)
  have b2 := vtx_val n hn j 2 (by norm_num)
  fin_cases t <;> fin_cases t' <;> simp [triEdge, Sym2.eq_iff, Fin.ext_iff] at h <;>
    rw [a0, a1, a2, b0, b1, b2] at * <;> split_ifs at * <;> omega

/-- **Lower bound** `|C_n², H| ≥ ⌈n/2⌉` for every triangle-free `H` and `n ≥ 5`. -/
theorem sq_lower {W : Type*} (hn : 5 ≤ n) {H : SimpleGraph W} [DecidableEq W] (hH : H.CliqueFree 3) :
    (((n + 1) / 2 : ℕ) : ℕ∞) ≤ nhf (sqCycle n) H := by
  classical
  apply le_nhf
  intro S ⟨g⟩
  have hit : ∀ i : Fin n, ∃ t, triEdge n hn i t ∈ S := by
    intro i
    by_contra hcon
    push Not at hcon
    obtain ⟨e01, e02, e12⟩ := tri_adj n hn i
    have kept : ∀ a b, (sqCycle n).Adj a b → s(a, b) ∉ S → H.Adj (g a) (g b) := fun a b h hs =>
      g.map_rel (by rw [deleteEdges_adj]; exact ⟨h, hs⟩)
    have k01 := kept _ _ e01 (by simpa [triEdge] using hcon 0)
    have k12 := kept _ _ e12 (by simpa [triEdge] using hcon 1)
    have k02 := kept _ _ e02 (by simpa [triEdge] using hcon 2)
    exact hH _ (is3Clique_triple_iff.mpr ⟨k01, k02, k12⟩)
  choose t ht using hit
  let E : Fin n → Sym2 (Fin n) := fun i => triEdge n hn i (t i)
  have hfib : ∀ e ∈ (univ : Finset (Fin n)).image E,
      ((univ : Finset (Fin n)).filter fun i => E i = e).card ≤ 2 := by
    intro e _
    by_contra hlt
    push Not at hlt
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := two_lt_card_iff.mp hlt
    simp only [mem_filter, mem_univ, true_and] at ha hb hc
    have r1 := pair_rel n hn a b _ _ (ha.trans hb.symm)
    have r2 := pair_rel n hn a c _ _ (ha.trans hc.symm)
    have r3 := pair_rel n hn b c _ _ (hb.trans hc.symm)
    have := a.isLt; have := b.isLt; have := c.isLt
    have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
    have hac' : a.val ≠ c.val := fun h => hac (Fin.ext h)
    have hbc' : b.val ≠ c.val := fun h => hbc (Fin.ext h)
    omega
  have hcard := card_le_mul_card_image (univ : Finset (Fin n)) 2 hfib
  have himg : ((univ : Finset (Fin n)).image E).card ≤ S.card :=
    card_le_card (fun e he => by obtain ⟨i, -, rfl⟩ := mem_image.mp he; exact ht i)
  rw [card_univ, Fintype.card_fin] at hcard
  have : (n + 1) / 2 ≤ S.card := by omega
  exact_mod_cast this

end NonHom
