# Non-homomorphism parameter of augmented Petersen graphs

We study the sequence G₀, G₁, G₂, G₃, G₄ where Gₖ is the Petersen graph
with k extra edges added, and compute |Gₖ, H|₀ for several targets H.

## Graph construction

The **Petersen graph** has 10 vertices and 15 edges:

- Outer pentagon: 0–1–2–3–4–0
- Spokes: 0–5, 1–6, 2–7, 3–8, 4–9
- Inner pentagram: 5–7, 7–9, 9–6, 6–8, 8–5

Every vertex has degree 3. The graph is vertex-transitive, edge-transitive,
and **a core** (every endomorphism is an automorphism).

The added edges are the five *skip-1* non-edges on the outer pentagon —
exactly the complement of the outer C₅, which is itself a C₅:

| Graph | Added edges | Total edges |
|-------|-------------|-------------|
| G₀ = Petersen | — | 15 |
| G₁ = PetGraph+1 | {0,2} | 16 |
| G₂ = PetGraph+2 | {0,2}, {1,3} | 17 |
| G₃ = PetGraph+3 | {0,2}, {1,3}, {2,4} | 18 |
| G₄ = PetGraph+4 | {0,2}, {1,3}, {2,4}, {0,3} | 19 |

All non-edges of the Petersen graph are automorphically equivalent (the
automorphism group S₅ acts transitively on them), so G₁ is unique up to
isomorphism. G₂, G₃, G₄ depend on the choice of subsequent edges; here we
always choose the next skip-1 outer pair.

---

## Results table

|Gₖ \ H | Petersen | K₂ | K₃ | K₄ | C₅ | G₁ | G₂ | G₃ |
|--------|----------|----|----|----|----|----|----|-----|
| G₀ (Petersen) | 0 | 3 | 0 | 0 | 2 | — | — | — |
| G₁ | **1** | 3 | 0 | 0 | 2 | — | — | — |
| G₂ | **2** | — | 0 | — | 2 | **0** | — | — |
| G₃ | **3** | — | 0 | — | 3 | **0** | **0** | — |
| G₄ | **3** | — | 1 | — | 3 | **1** | **1** | **1** |

All values computed by the bitmask branch-and-bound solver in
`src/main.rs` (release build, 12 threads), in milliseconds.

---

## Observations

### → Petersen (core target)

|Gₖ, Petersen|₀ = 0, 1, 2, 3, **3** for k = 0,1,2,3,4.

The parameter grows linearly from k=0 to k=3, then **plateaus at 3** for k=4.
The naive prediction of 4 for G₄ fails because we are free to remove *original*
Petersen edges as well as added ones. Removing one original edge can break the
endomorphism-forces-automorphism constraint and open a non-automorphic
homomorphism path to Petersen that satisfies all four added non-edges simultaneously.

The core property of the Petersen graph guarantees |G₁, Petersen|₀ ≥ 1 (any
endomorphism is an automorphism, automorphisms preserve non-edges, so no
homomorphism G₁ → Petersen exists). The same argument applies to G₂ and G₃.
For G₄ the optimal strategy involves at least one original-edge removal.

### → K₃ (3-colourability)

The Petersen graph has a valid 3-colouring:

```
0→1, 1→2, 2→3, 3→1, 4→2
5→2, 6→1, 7→1, 8→3, 9→3
```

In this colouring the pairs {0,2}, {1,3}, {2,4} all receive **different colours**,
so G₁, G₂, G₃ remain 3-colourable and |Gₖ, K₃|₀ = 0 for k ≤ 3.

Adding edge {0,3} in G₄ creates a problem: 0→1 and 3→1, **same colour**.
The outer-vertex subgraph of G₄ is K₅ − {1,4}, which has χ = 4, making G₄
not 3-colourable. Removing one of the four added edges (e.g. restoring G₃)
recovers a valid 3-colouring, so |G₄, K₃|₀ = **1**.

### → C₅

|Gₖ, C₅|₀ = 2, 2, 2, **3**, 3 for k = 0,1,2,3,4.

The parameter is flat at 2 for k ≤ 2, then jumps to 3 at k=3 (adding {2,4}
disrupts the best C₅-homomorphism), and stays at 3 for k=4. Adding edges to G
can never decrease |G, H|₀.

### → Gⱼ (augmented Petersen as target)

The behaviour here reveals which augmented graphs are **cores**:

- **G₁ and G₂ are not cores**: G₂ maps to G₁ with 0 removals, G₃ maps to both
  G₁ and G₂ with 0 removals. Non-automorphic endomorphisms exist that map
  additional non-edges onto the available extra edges.
- **G₃ appears to behave like a core** relative to the edge {0,3}: no
  endomorphism of G₃ can map the pair (0,3) to an edge, so
  |G₄, G₃|₀ = 1 > 0. Removing {0,3} from G₄ recovers G₃ (identity
  homomorphism), confirming the value is exactly 1.

### Summary of surprises

| Prediction | Actual | Explanation |
|------------|--------|-------------|
| \|G₄, Petersen\|₀ = 4 | **3** | Original-edge removal enables non-automorphic hom |
| \|G₄, K₃\|₀ = 0 | **1** | G₄ is 4-chromatic (outer subgraph K₅−{1,4} has χ=4) |
| \|Gₖ, Gⱼ\|₀ = 1 for j < k | **0** (for j=1,2; k=2,3) | G₁ and G₂ are not cores |
