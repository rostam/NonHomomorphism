# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a graph theory research project studying **graph homomorphisms** and **non-homomorphism factors**. The core concept is `|G,H|`: the minimum number of edges to remove from graph G so that a homomorphism G→H exists. A new **concentration parameter** γ(G,H) is also being developed, measuring the minimum (over all homomorphisms) of the maximum number of G-edges mapped to any single H-edge.

Implementations exist in three languages — Python (primary), C++, and Rust — all solving the same core problem with different approaches.

## Build & Run Commands

### Python
```bash
cd SourceCode
python -m unittest TestHomomorphism.py         # run tests
python FindHomomorphisms.py                    # core homomorphism finder
python any_homomorphism_to_triangle.py         # triangle analysis
python vis_fast.py                             # aggregate graph collections
python diff.py <file1> <file2> <output>        # graph set difference by line
python gset_subtaction.py                      # graph set subtraction on .g6 files
```

Python dependencies: `networkx`, `more_itertools`, `matplotlib`

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
cargo build --release
```

## Architecture

### Core Algorithms

All three implementations share the same backtracking search strategy for homomorphism detection: try all vertex mappings from G to H, validating that each edge in G maps to an edge in H.

**Python** (`FindHomomorphisms.py`): partition-based approach — generates set partitions of G's vertices, where vertices in the same partition share a target. Uses `more_itertools.set_partitions`.

**C++** (`CPP/main.cpp`): DFS with adjacency list graphs. Also implements `estimate_non_homomorphism_factor(G, H, max_k)`, which iterates k=0..max_k, enumerating all C(|E(G)|,k) edge subsets to remove, testing each for homomorphism.

**Rust** (`RustFiles/homomorphism/src/main.rs`): recursive backtracking using `petgraph` for graph representation.

### Test Data

`.g6` files in `SourceCode/` contain graphs in **Graph6 format** (a compact ASCII encoding). Files are named by vertex count: `n2.g6` through `n8.g6`. Variants `nX_trees.g6` and `nX_no_trees.g6` contain filtered subsets. These are used as target graphs in Python tests and analysis scripts.

### Graph Sets Used in Tests

`TestHomomorphism.py` loads graph targets from `.g6` files and tests the Petersen graph (10 vertices, 3-regular) against various targets. The Python scripts treat `.g6` files as line-delimited graph collections that can be manipulated with set operations.
