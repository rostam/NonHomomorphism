"""
extended_experiments.py -- Extended computational results for the paper.

Computes γ(G,H) and |G,H| for:
  1. Irregular source graphs (wheel, friendship, book, complete multipartite)
  2. Non-complete target graphs (odd cycles, Petersen graph)
  3. Kneser graphs
"""

import math
import time
from itertools import combinations
from math import comb, ceil

import networkx as nx

from analysis import gamma_nx


# ─────────────────────────────────────────────────────────────────────────────
# Graph builders
# ─────────────────────────────────────────────────────────────────────────────

def friendship_graph(k):
    """Friendship graph F_k: k triangles sharing a common hub vertex.
    Vertices: 2k+1, Edges: 3k.  Irregular: hub has degree 2k, others degree 2.
    Chromatic number: 3 (contains a triangle, is 3-colourable)."""
    G = nx.Graph()
    G.add_node(0)
    for i in range(k):
        u, v = 2 * i + 1, 2 * i + 2
        G.add_edges_from([(0, u), (0, v), (u, v)])
    G.graph["name"] = f"F_{k}"
    return G


def book_graph(k):
    """Book graph B_k: k triangles sharing a common edge {0,1}.
    Vertices: k+2, Edges: 2k+1.  Irregular: spine vertices have degree k+1,
    page vertices have degree 2.  Chromatic number: 3 (contains triangle)."""
    G = nx.Graph()
    G.add_edge(0, 1)
    for i in range(k):
        v = i + 2
        G.add_edges_from([(0, v), (1, v)])
    G.graph["name"] = f"B_{k}"
    return G


# ─────────────────────────────────────────────────────────────────────────────
# Helper: fast homomorphism existence check + NHF
# ─────────────────────────────────────────────────────────────────────────────

def find_hom(G, H):
    """Return True iff a homomorphism G -> H exists (backtracking)."""
    nG = G.number_of_nodes()
    G_nodes = list(G.nodes())
    H_nodes = list(H.nodes())
    H_adj = set()
    for u, v in H.edges():
        H_adj.add((u, v))
        H_adj.add((v, u))

    node_idx = {v: i for i, v in enumerate(G_nodes)}
    mapping = [-1] * nG

    def bt(i):
        if i == nG:
            return True
        for hv in H_nodes:
            ok = True
            for nb in G.neighbors(G_nodes[i]):
                idx = node_idx[nb]
                if mapping[idx] != -1 and (hv, mapping[idx]) not in H_adj:
                    ok = False
                    break
            if ok:
                mapping[i] = hv
                if bt(i + 1):
                    return True
                mapping[i] = -1
        return False

    return bt(0)


def nhf(G, H, max_k=6):
    """Non-homomorphism factor |G,H| via edge-removal search up to max_k."""
    edges = list(G.edges())
    m = len(edges)
    for k in range(0, min(max_k + 1, m + 1)):
        for combo in combinations(range(m), k):
            G2 = G.copy()
            for i in combo:
                G2.remove_edge(*edges[i])
            if find_hom(G2, H):
                return k
    return None  # not found within max_k


def gamma_or_inf(G, H):
    """Return γ(G,H), or None if no homomorphism exists."""
    return gamma_nx(G, H)


def deg_seq_str(G):
    """Compact degree-sequence string."""
    degs = sorted(dict(G.degree()).values(), reverse=True)
    return str(degs)


# ─────────────────────────────────────────────────────────────────────────────
# 1.  Irregular source graphs → complete targets
# ─────────────────────────────────────────────────────────────────────────────

def run_irregular_sources():
    print("=" * 75)
    print("Table A: Irregular source graphs → complete targets")
    print("=" * 75)

    K2 = nx.complete_graph(2)
    K3 = nx.complete_graph(3)
    K4 = nx.complete_graph(4)
    K5 = nx.complete_graph(5)

    rows = []

    # Wheel graphs W_n = wheel_graph(n), hub + C_{n-1}
    # chi = 4 if (n-1) is odd, chi = 3 if (n-1) is even
    for n in [5, 6, 7, 8, 9]:
        W = nx.wheel_graph(n)
        nv, ne = W.number_of_nodes(), W.number_of_edges()
        chi = 4 if (n - 1) % 2 == 1 else 3
        for m, Km in [(2, K2), (3, K3), (4, K4)]:
            g = gamma_or_inf(W, Km)
            n_hf = nhf(W, Km, 6)
            rows.append((f"W_{n}", nv, ne, chi, f"K_{m}", n_hf, g))

    # Friendship graphs F_k
    for k in range(2, 8):
        F = friendship_graph(k)
        nv, ne = F.number_of_nodes(), F.number_of_edges()
        for m, Km in [(2, K2), (3, K3)]:
            g = gamma_or_inf(F, Km)
            n_hf = nhf(F, Km, 6)
            rows.append((f"F_{k}", nv, ne, 3, f"K_{m}", n_hf, g))

    # Book graphs B_k
    for k in range(2, 8):
        B = book_graph(k)
        nv, ne = B.number_of_nodes(), B.number_of_edges()
        for m, Km in [(2, K2), (3, K3)]:
            g = gamma_or_inf(B, Km)
            n_hf = nhf(B, Km, 6)
            rows.append((f"B_{k}", nv, ne, 3, f"K_{m}", n_hf, g))

    # Complete multipartite (irregular when parts unequal)
    for parts, label in [
        ((2, 3, 4), "K_{2,3,4}"),
        ((1, 2, 3), "K_{1,2,3}"),
        ((2, 2, 3), "K_{2,2,3}"),
    ]:
        G = nx.complete_multipartite_graph(*parts)
        nv, ne = G.number_of_nodes(), G.number_of_edges()
        for m, Km in [(3, K3), (4, K4)]:
            g = gamma_or_inf(G, Km)
            n_hf = nhf(G, Km, 6)
            rows.append((label, nv, ne, 3, f"K_{m}", n_hf, g))

    # Print table
    print(f"{'G':>12} {'|V|':>4} {'|E|':>4} {'χ':>3} {'H':>6} "
          f"{'|G,H|':>6} {'γ(G,H)':>8} {'⌈|E|/|E(H)|⌉':>14}")
    print("-" * 70)
    eH_map = {"K_2": 1, "K_3": 3, "K_4": 6, "K_5": 10}
    for (gname, nv, ne, chi, hname, n_hf, g) in rows:
        eH = eH_map[hname]
        ph = ceil(ne / eH) if g is not None else "---"
        nhf_s = str(n_hf) if n_hf is not None else ">6"
        g_s = str(g) if g is not None else "+∞"
        print(f"  {gname:>10} {nv:4d} {ne:4d} {chi:3d} {hname:>6} "
              f"{nhf_s:>6} {g_s:>8} {str(ph):>14}")

    print()
    return rows


# ─────────────────────────────────────────────────────────────────────────────
# 2.  Non-complete target graphs
# ─────────────────────────────────────────────────────────────────────────────

def run_non_complete_targets():
    print("=" * 75)
    print("Table B: γ for cycles mapping to odd-cycle targets")
    print("=" * 75)

    C5 = nx.cycle_graph(5)
    C7 = nx.cycle_graph(7)
    P = nx.petersen_graph()

    rows = []

    # Cycles -> C5
    print("\n--- Cycles → C_5 (5 edges, χ=3) ---")
    print(f"{'C_n':>6} {'γ(C_n,C_5)':>12} {'⌈n/5⌉':>8}")
    print("-" * 30)
    for n in range(3, 16):
        G = nx.cycle_graph(n)
        g = gamma_or_inf(G, C5)
        ph = ceil(n / 5) if g is not None else "---"
        g_s = str(g) if g is not None else "+∞"
        print(f"  C_{n:<3} {g_s:>12} {str(ph):>8}")
        rows.append(("C_" + str(n), n, "C_5", g, ceil(n / 5) if g is not None else None))

    # Cycles -> C7
    print("\n--- Cycles → C_7 (7 edges, χ=3) ---")
    print(f"{'C_n':>6} {'γ(C_n,C_7)':>12} {'⌈n/7⌉':>8}")
    print("-" * 30)
    for n in range(3, 16):
        G = nx.cycle_graph(n)
        g = gamma_or_inf(G, C7)
        ph = ceil(n / 7) if g is not None else "---"
        g_s = str(g) if g is not None else "+∞"
        print(f"  C_{n:<3} {g_s:>12} {str(ph):>8}")

    # Cycles -> Petersen
    print("\n--- Cycles → Petersen (15 edges, χ=3) ---")
    print(f"{'C_n':>6} {'γ(C_n,P)':>12} {'⌈n/15⌉':>8}")
    print("-" * 30)
    for n in range(3, 13):
        G = nx.cycle_graph(n)
        g = gamma_or_inf(G, P)
        ph = ceil(n / 15) if g is not None else "---"
        g_s = str(g) if g is not None else "+∞"
        print(f"  C_{n:<3} {g_s:>12} {str(ph):>8}")

    print()
    return rows


# ─────────────────────────────────────────────────────────────────────────────
# 3.  Kneser graphs
# ─────────────────────────────────────────────────────────────────────────────

def run_kneser():
    print("=" * 75)
    print("Table C: Kneser graphs")
    print("=" * 75)

    K3 = nx.complete_graph(3)
    K4 = nx.complete_graph(4)

    # Kneser(5,2) = Petersen (chi=3, 10v, 15e)
    KN52 = nx.kneser_graph(5, 2)
    print(f"Kneser(5,2) = Petersen: {KN52.number_of_nodes()}v, "
          f"{KN52.number_of_edges()}e, "
          f"isomorphic to Petersen: {nx.is_isomorphic(KN52, nx.petersen_graph())}")
    g3 = gamma_or_inf(KN52, K3)
    print(f"  γ(Kneser(5,2), K3) = {g3}")

    # Kneser(6,2) (chi=4, 15v, 45e)
    KN62 = nx.kneser_graph(6, 2)
    print(f"\nKneser(6,2): {KN62.number_of_nodes()}v, "
          f"{KN62.number_of_edges()}e, χ = 4")
    g3 = gamma_or_inf(KN62, K3)
    print(f"  γ(Kneser(6,2), K3) = {g3} (expected +∞, since χ(K(6,2))=4 > 3)")
    t0 = time.time()
    g4 = gamma_or_inf(KN62, K4)
    print(f"  γ(Kneser(6,2), K4) = {g4}  (time = {time.time()-t0:.1f}s)")
    n_hf3 = nhf(KN62, K3, 6)
    print(f"  |Kneser(6,2), K3| = {n_hf3}")

    print()


# ─────────────────────────────────────────────────────────────────────────────
# 4.  Lemma verification on extended results
# ─────────────────────────────────────────────────────────────────────────────

def run_verification():
    print("=" * 75)
    print("Lemma verification on extended results")
    print("=" * 75)

    K3 = nx.complete_graph(3)
    K4 = nx.complete_graph(4)
    K2 = nx.complete_graph(2)

    # Multiplicativity: γ(G,K) ≤ γ(G,H)·γ(H,K)
    print("\n--- Multiplicativity (Lemma 3.4) ---")
    # F_4 -> K3 -> K4: γ(F4,K4) ≤ γ(F4,K3)·γ(K3,K4)
    F4 = friendship_graph(4)
    gF4K3 = gamma_or_inf(F4, K3)
    gK3K4 = gamma_or_inf(K3, K4)
    gF4K4 = gamma_or_inf(F4, K4)
    ok = gF4K4 <= gF4K3 * gK3K4
    print(f"  γ(F_4,K4)={gF4K4} ≤ γ(F_4,K3)·γ(K3,K4)={gF4K3}·{gK3K4}"
          f"={gF4K3 * gK3K4}: {'✓' if ok else '✗'}")

    # Wheel -> K3 -> K4
    W7 = nx.wheel_graph(7)
    gW7K3 = gamma_or_inf(W7, K3)
    gW7K4 = gamma_or_inf(W7, K4)
    ok = gW7K4 <= gW7K3 * gK3K4
    print(f"  γ(W_7,K4)={gW7K4} ≤ γ(W_7,K3)·γ(K3,K4)={gW7K3}·{gK3K4}"
          f"={gW7K3 * gK3K4}: {'✓' if ok else '✗'}")

    # Bound on NHF: |G,K| ≤ γ(G,H)·|H,K|
    print("\n--- NHF Bound (Lemma 3.5) ---")
    # |F_4,K2| ≤ γ(F_4,K3)·|K3,K2|
    nhfF4K2 = nhf(F4, K2, 6)
    nhfK3K2 = nhf(K3, K2, 3)
    ok = nhfF4K2 <= gF4K3 * nhfK3K2
    print(f"  |F_4,K2|={nhfF4K2} ≤ γ(F_4,K3)·|K3,K2|={gF4K3}·{nhfK3K2}"
          f"={gF4K3 * nhfK3K2}: {'✓' if ok else '✗'}")

    # |W_7,K2| ≤ γ(W_7,K3)·|K3,K2|
    nhfW7K2 = nhf(W7, K2, 6)
    ok = nhfW7K2 <= gW7K3 * nhfK3K2
    print(f"  |W_7,K2|={nhfW7K2} ≤ γ(W_7,K3)·|K3,K2|={gW7K3}·{nhfK3K2}"
          f"={gW7K3 * nhfK3K2}: {'✓' if ok else '✗'}")

    # Monotonicity: H1 ⊂ H2 => γ(G,H2) ≤ γ(G,H1)
    print("\n--- Monotonicity (Lemma 3.7) ---")
    for gname, G in [("F_4", F4), ("W_7", W7), ("B_5", book_graph(5))]:
        g3 = gamma_or_inf(G, K3)
        g4 = gamma_or_inf(G, K4)
        if g3 is not None and g4 is not None:
            ok = g4 <= g3
            print(f"  γ({gname},K4)={g4} ≤ γ({gname},K3)={g3}: "
                  f"{'✓' if ok else '✗'}")

    print()


# ─────────────────────────────────────────────────────────────────────────────
# Main
# ─────────────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    run_irregular_sources()
    run_non_complete_targets()
    run_kneser()
    run_verification()
