import NonHom.Defs

/-!
# Section 1 of the paper: cited background facts

Proposition `prop:chi_mono` and Theorem `thm:hom_contracts` (both cited from
Hell–Nešetřil) are re-proved here. Theorem `thm:vertex_trans` (the no-homomorphism lemma
for vertex-transitive targets) is cited and not formalized.
-/

open SimpleGraph

namespace NonHom

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Proposition `prop:chi_mono`: `G → H` implies `χ(G) ≤ χ(H)`. -/
theorem chromaticNumber_le_of_hom (f : G →g H) : G.chromaticNumber ≤ H.chromaticNumber :=
  chromaticNumber_mono_of_hom f

/-- Theorem `thm:hom_contracts`: homomorphisms do not increase (extended) distances. -/
theorem edist_map_le (f : G →g H) (u v : V) : H.edist (f u) (f v) ≤ G.edist u v := by
  by_cases h : G.Reachable u v
  · obtain ⟨p, hp⟩ := h.exists_walk_length_eq_edist
    rw [← hp]
    calc H.edist (f u) (f v) ≤ (p.map f).length := edist_le _
      _ = p.length := by rw [Walk.length_map]
  · rw [edist_eq_top_of_not_reachable h]; exact le_top

/-- Theorem `thm:hom_contracts`, for the (finite) distance between reachable vertices. -/
theorem dist_map_le (f : G →g H) {u v : V} (h : G.Reachable u v) :
    H.dist (f u) (f v) ≤ G.dist u v := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  rw [← hp]
  exact (dist_le (p.map f)).trans (by rw [Walk.length_map])

end NonHom
