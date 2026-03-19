import more_itertools as miter
import itertools as iter
import networkx as nx


def find_a_homomorphism(G, H, num_of_subsets=None):
    """Find a homomorphism from G to H using a set-partition approach.

    Partitions V(G) into groups where vertices in the same group map to the
    same vertex in H.  Returns the partition (list of lists of vertex labels)
    on success, or an empty list if no homomorphism exists.

    If num_of_subsets is given, only partitions of exactly that size are tried.
    Otherwise all sizes from 1 to |V(H)| are tried.
    """
    if num_of_subsets is None:
        for k in range(1, len(H.nodes()) + 1):
            result = find_a_homomorphism(G, H, k)
            if result:
                return result
        return []

    G_nodes = list(G.nodes())
    size_of_set = len(G_nodes)

    # Represent vertices as sequential integers 0, 1, ..., size_of_set-1.
    # (Handles graphs whose vertex labels are not 0-based.)
    node_to_idx = {v: i for i, v in enumerate(G_nodes)}
    iterable = list(range(size_of_set))

    for part in miter.set_partitions(iterable, num_of_subsets):
        # Check: no two vertices in the same partition class are adjacent in G
        # (they would both map to the same H-vertex, creating a loop).
        valid = True
        for p in part:
            if len(p) < 2:
                continue
            for v1, v2 in iter.combinations(p, 2):
                if G.has_edge(G_nodes[v1], G_nodes[v2]):
                    valid = False
                    break
            if not valid:
                break

        if not valid:
            continue

        # Check: for each pair of partition classes (i, j) that are NOT
        # connected by an edge in H, no G-edge crosses from class i to class j.
        for (ci, pi), (cj, pj) in iter.combinations(enumerate(part), 2):
            if not valid:
                break
            if not H.has_edge(ci, cj):
                for v1 in pi:
                    if not valid:
                        break
                    for v2 in pj:
                        if G.has_edge(G_nodes[v1], G_nodes[v2]):
                            valid = False
                            break

        if valid:
            return part

    return []


def handle_one_g6_string(G, g6_string_H):
    """Find a homomorphism from G to the graph encoded by g6_string_H."""
    H = nx.from_graph6_bytes(bytes(g6_string_H, 'ascii'))
    for j in range(1, len(H) + 1):
        part = find_a_homomorphism(G, H, j)
        if part:
            return part
    return []
