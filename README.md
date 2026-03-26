# Non-Homomorphism Factors and the Concentration Parameter in Graph Homomorphisms

**Author:** Mohammad Ali Rostami

This repository contains the paper, source code, and computational experiments for studying two measures associated with graph homomorphisms: the *non-homomorphism factor* $|G,H|$ and the *concentration parameter* $\gamma(G,H)$.

---

## Overview

A **homomorphism** from graph $G$ to graph $H$ is a function $f\colon V(G)\to V(H)$ such that $\{u,v\}\in E(G)$ implies $\{f(u),f(v)\}\in E(H)$. We write $G\to H$ when such a function exists. A proper $k$-colouring of $G$ exists if and only if $G\to K_k$, so $G\to H \Rightarrow \chi(G)\le\chi(H)$.

This project studies:
1. **Non-homomorphism factor** $|G,H|$: the minimum number of edges to remove from $G$ so that a homomorphism $G\to H$ exists.
2. **Concentration parameter** $\gamma(G,H)$: the minimum, over all homomorphisms $f\colon G\to H$, of the maximum number of $G$-edges mapped to any single $H$-edge.

## Key Results

### Non-Homomorphism Factor

The non-homomorphism factor $|G,H|$ was introduced by Khoshkha [[1]](#1). Key properties:
- $H_1 \to H_2 \Rightarrow |G,H_1| \geq |G,H_2|$ for every graph $G$
- $H_1 \leftrightarrow H_2 \Rightarrow |G,H_1| = |G,H_2|$ for every $G$
- If $f\colon G_1 \to G_2$ is edge-injective, then $|G_1,H| \leq |G_2,H|$ for every $H$

**Turán connection.** We prove $|K_n,K_m| = \binom{n}{2} - t(n,m)$ via Turán's theorem, where $t(n,m)$ is the number of edges in the Turán graph $T(n,m)$. In particular, $|K_{n+1},K_n|=1$ for all $n\ge 1$.

| $\|K_n,K_m\|$ | $K_2$ | $K_3$ | $K_4$ | $K_5$ | $K_6$ |
|:---:|:---:|:---:|:---:|:---:|:---:|
| $K_2$ | 0 | 0 | 0 | 0 | 0 |
| $K_3$ | 1 | 0 | 0 | 0 | 0 |
| $K_4$ | 2 | 1 | 0 | 0 | 0 |
| $K_5$ | 4 | 2 | 1 | 0 | 0 |
| $K_6$ | 6 | 3 | 2 | 1 | 0 |
| $K_7$ | 9 | 5 | 3 | 2 | 1 |

**General lower bound.** For any graphs $G$ and $H$:
$$|G,H| \;\ge\; \max\!\bigl(0,\;|E(G)|-t(|V(G)|,\chi(H))\bigr)$$

### Concentration Parameter

We introduce the **concentration parameter** $\gamma(G,H)$, which measures the unavoidable edge congestion under homomorphisms. When $G\not\to H$, we set $\gamma(G,H)=+\infty$.

**Proven properties:**
- $\gamma(G,G) = 1$ for any graph with at least one edge
- **Pigeonhole bound:** $\gamma(G,H) \ge \lceil|E(G)|/|E(H)|\rceil$
- **Multiplicativity:** $\gamma(G,K) \le \gamma(G,H) \cdot \gamma(H,K)$ when $G\to H\to K$
- **Monotonicity in target:** If $H_1 \subseteq H_2$ and $G\to H_1$, then $\gamma(G,H_2) \le \gamma(G,H_1)$
- **Bound on non-homomorphism factor:** If $G\to H$, then $|G,K| \le \gamma(G,H) \cdot |H,K|$

**d-Regularity formula.** For a $d$-regular graph $G$ on $n$ vertices with $\chi(G)=3$:
$$\gamma(G,K_3) = \frac{d}{2} \cdot M, \quad M = \min\bigl\{\max(s_1,s_2,s_3) : s_1+s_2+s_3=n,\; s_i\ge 0,\; s_1\equiv s_2\equiv s_3\pmod{2}\bigr\}$$

**Exact cycle formula** (verified computationally for $n\le 50$):
$$\gamma(C_n, K_3) = \begin{cases} \lceil n/3 \rceil & \text{if } n \not\equiv 2 \pmod{3} \\\\ \lceil n/3 \rceil + 1 & \text{if } n \equiv 2 \pmod{3} \end{cases}$$

| $C_n$ | $\|E\|$ | $\|C_n,K_3\|$ | $\gamma(C_n,K_3)$ | Pigeonhole |
|:---:|:---:|:---:|:---:|:---:|
| $C_3$ | 3 | 0 | 1\* | 1 |
| $C_4$ | 4 | 0 | 2\* | 2 |
| $C_5$ | 5 | 0 | 3 | 2 |
| $C_6$ | 6 | 0 | 2\* | 2 |
| $C_7$ | 7 | 0 | 3\* | 3 |
| $C_8$ | 8 | 0 | 4 | 3 |
| $C_9$ | 9 | 0 | 3\* | 3 |

(\* = achieves pigeonhole bound)

**Complete bipartite graphs:** $\gamma(K_{n,n}, K_3) = n\cdot\lceil n/2\rceil$.

**Petersen graph:**

| $H$ | $\|E(H)\|$ | $\|P,H\|$ | $\gamma(P,H)$ | Pigeonhole |
|:---:|:---:|:---:|:---:|:---:|
| $K_2$ | 1 | 3 | $+\infty$ | — |
| $K_3$ | 3 | 0 | 6 | 5 |
| $K_4$ | 6 | 0 | 4 | 3 |
| $K_5$ | 10 | 0 | 2 | 2 |

The value $\gamma(P,K_3)=6$ exceeds the pigeonhole bound of 5 due to the parity obstruction in the $d$-regularity formula ($n=10$, $d=3$).

### The Symmetric Combination $m(G,H)$

Define $m(G,H) = \max(|G,H|,\,|H,G|)$. This function is non-negative, satisfies $m(G,G)=0$, is symmetric, and $m(G,H)=0$ iff $G$ and $H$ are homomorphically equivalent (i.e., $\operatorname{core}(G) \cong \operatorname{core}(H)$).

**The triangle inequality fails.** Contrary to a prior claim by Khoshkha [[1]](#1), $m$ does *not* satisfy the triangle inequality:
$$m(K_7,K_3) = 5 > 4 = m(K_7,K_5) + m(K_5,K_3)$$

A systematic search found **108 counterexample triples** among complete graphs with at most 10 vertices.

### Extended Results

**Irregular source graphs:**
- **Friendship graphs** $F_k$: $\gamma(F_k, K_3) = k$ — exactly achieves the pigeonhole bound $\lceil 3k/3 \rceil = k$.
- **Book graphs** $B_k$: $\gamma(B_k, K_3) = k$ but $|B_k, K_2| = 1$, demonstrating that $\gamma$ (local congestion) and $|G,H|$ (global fragility) capture fundamentally different properties.
- **Wheel graphs** $W_n$: $\gamma$ strictly exceeds the pigeonhole bound due to the high-degree hub vertex (e.g., $\gamma(W_7, K_3) = 6$ vs. pigeonhole of 4).
- **Complete multipartite graphs:** $\gamma(K_{a,b,c}, K_3) = \max(ab, ac, bc)$.

**Non-complete targets:** Experiments with odd cycles ($C_5$, $C_7$) and the Petersen graph as targets show that $\gamma(C_n, C_5)$ achieves the pigeonhole bound when $5\mid n$ and exceeds it otherwise, and $\gamma(C_n, P)$ is remarkably low (often 1) due to the Petersen graph's high symmetry.

**Kneser graphs:** $K(5,2)$ (the Petersen graph) yields $\gamma(K(5,2),K_3)=6$. $K(6,2)$ has $\chi=4$, giving $|K(6,2),K_3|=3$ and $\gamma(K(6,2),K_4)=9$ (exceeding the pigeonhole bound of 8).

## Open Questions

1. **Extend the $d$-regularity formula to general $H$.** Can the formula be generalised when $H$ has multiple edge orbits?
2. **When does $\gamma(G,H)$ meet the pigeonhole bound?** The parity obstruction raises $\gamma$ for certain congruence classes — is this the only obstruction?
3. **Can $m$ be repaired into a metric?** Can an edge-edit distance variant or other modification restore the triangle inequality?
4. **$\gamma$ and the fractional chromatic number.** Is $\gamma(G,K_m)$ related to $\chi_f(G)$ for vertex-transitive $G$?
5. **Characterise sub-additivity triples.** Which triples $(G,H,K)$ satisfy $|G,K| \le |G,H| + |H,K|$?

## Repository Structure

```
├── Paper/
│   ├── paper.tex              # LaTeX source of the paper
│   └── paper.pdf              # Compiled paper
├── SourceCode/
│   ├── FindHomomorphisms.py   # Core homomorphism finder (partition-based, Python/NetworkX)
│   ├── homomorphism.py        # Homomorphism utilities
│   ├── analysis.py            # Theoretical analysis: γ(C_n,K_3) via DP, d-regularity, triangle-inequality search
│   ├── extended_experiments.py# Extended experiments: wheels, friendship/book graphs, Kneser, non-complete targets
│   ├── TestHomomorphism.py    # Unit tests for homomorphism algorithms
│   ├── any_homomorphism_to_triangle.py  # Triangle homomorphism analysis
│   ├── vis_fast.py            # Graph6 file aggregation utility
│   ├── diff.py                # Set difference on graph files
│   ├── gset_subtaction.py     # Graph set subtraction on .g6 files
│   ├── *.g6                   # Graph6 test data (n2 through n8, trees/no-trees variants)
│   ├── CPP/
│   │   ├── main.cpp           # C++ homomorphism & non-homomorphism factor (backtracking DFS)
│   │   ├── experiments.cpp    # C++ computational experiments (complete tables, γ computation)
│   │   └── CMakeLists.txt
│   └── RustFiles/
│       └── homomorphism/
│           └── src/main.rs    # Rust homomorphism finder (petgraph, backtracking)
```

## Build & Run

### Python
```bash
cd SourceCode
python -m unittest TestHomomorphism.py         # Run tests
python FindHomomorphisms.py                    # Core homomorphism finder
python analysis.py                             # Theoretical analysis & verification
python extended_experiments.py                 # Extended computational experiments
```
Dependencies: `networkx`, `more_itertools`, `matplotlib`

### C++
```bash
cd SourceCode/CPP
cmake -B cmake-build-debug
cmake --build cmake-build-debug
./cmake-build-debug/CPP
```
Requires C++26 (GCC 13+/Clang 17+) and CMake 3.31+.

### Rust
```bash
cd SourceCode/RustFiles/homomorphism
cargo run --release
```

## References

<a id="1">[1]</a>
K. Khoshkha, *Nonhomomorphism Factors*, M.Sc. thesis, Sharif University of Technology, 2005. [Thesis link](http://library.sharif.ir/parvan/resource/286721/)

<a id="2">[2]</a>
A. Daneshgar and H. Hajiabolhassan, "Circular colouring and algebraic no-homomorphism theorems," *European Journal of Combinatorics*, vol. 28, no. 6, pp. 1843–1853, 2007. [DOI](https://doi.org/10.1016/j.ejc.2006.04.010)

<a id="3">[3]</a>
A. Daneshgar and H. Hajiabolhassan, "Graph homomorphisms through random walks," *Journal of Graph Theory*, vol. 44, pp. 15–38, 2003.

<a id="4">[4]</a>
P. Hell and J. Nešetřil, *Graphs and Homomorphisms*, Oxford University Press, 2004.

<a id="5">[5]</a>
Y. Shitov, "Counterexamples to Hedetniemi's conjecture," *Annals of Mathematics*, vol. 190, no. 2, pp. 663–667, 2019.
