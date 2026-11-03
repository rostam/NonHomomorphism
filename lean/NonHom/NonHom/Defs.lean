import Mathlib

/-!
# Definitions: non-homomorphism factor `|G,H|` and concentration parameter `γ(G,H)`

These follow `Paper/paper.tex`, Definitions `def:nhf` and `def:gamma`.

* `NonHom.nhf G H : ℕ∞` is the least number of edges to delete from `G` so that a
  homomorphism into `H` exists (`⊤` if no finite deletion works, e.g. `H` has no vertices).
* `NonHom.load f e` is the number of `G`-edges mapped by the homomorphism `f` onto `e`.
* `NonHom.mu f` is the maximum load over the images of the `G`-edges.
* `NonHom.gamma G H : ℕ∞` is the minimum of `mu f` over all homomorphisms `f : G →g H`
  (`⊤` if there is none).
-/

open SimpleGraph Finset

namespace NonHom

variable {V W X : Type*}

/-- The set of achievable deletion counts. -/
def nhfSet (G : SimpleGraph V) (H : SimpleGraph W) : Set ℕ∞ :=
  {k | ∃ S : Finset (Sym2 V), Nonempty (G.deleteEdges ↑S →g H) ∧ (S.card : ℕ∞) = k}

/-- The non-homomorphism factor `|G,H|`. -/
noncomputable def nhf (G : SimpleGraph V) (H : SimpleGraph W) : ℕ∞ :=
  sInf (nhfSet G H)

section load

variable [Fintype V] [DecidableEq W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W}

/-- The load of `e` under `f`: the number of `G`-edges mapped onto `e`. -/
def load (f : G →g H) (e : Sym2 W) : ℕ :=
  (G.edgeFinset.filter fun e' => e'.map f = e).card

/-- Maximum edge multiplicity `μ(f)`. -/
def mu (f : G →g H) : ℕ :=
  G.edgeFinset.sup fun e' => load f (e'.map f)

end load

/-- The concentration parameter `γ(G,H)`. -/
noncomputable def gamma [Fintype V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) : ℕ∞ :=
  ⨅ f : G →g H, (mu f : ℕ∞)

/-- The symmetric combination `m(G,H) = max(|G,H|, |H,G|)` (Definition `def:m`). -/
noncomputable def msym (G : SimpleGraph V) (H : SimpleGraph W) : ℕ∞ :=
  max (nhf G H) (nhf H G)

end NonHom
