"""Generate a varied 'zoo' of graphs (mostly NOT cores) for the profile space.

For each graph we compute omega, chi (exact, DSATUR branch and bound), odd
girth, and an exact shortcut when the homomorphism class is obvious:
  bipartite                  ->  K2
  chi = omega = k <= 8       ->  K_k
  omega = 2, odd girth g <= 11, G -> C_g   ->  C_g
Graphs without a shortcut get their profile from the Rust solver
(code/gp_profiles, mode 'list').

Usage:  python zoo_graphs.py
Writes  data/zoo_graphs.txt (name|family|n|u-v,...)  and  data/zoo_meta.csv
"""
import csv
import itertools
import pathlib
import random
import sys
from collections import deque

sys.setrecursionlimit(100000)
ROOT = pathlib.Path(__file__).resolve().parent.parent
DATA = ROOT / "data"


# ── constructors ──────────────────────────────────────────────────────────────
class G:
    def __init__(self, n, edges=()):
        self.n = n
        self.adj = [set() for _ in range(n)]
        for u, v in edges:
            self.add(u, v)

    def add(self, u, v):
        if u != v:
            self.adj[u].add(v); self.adj[v].add(u)

    def edges(self):
        return [(u, v) for u in range(self.n) for v in self.adj[u] if u < v]


def from_pairs(vertices, adjacent):
    idx = {v: i for i, v in enumerate(vertices)}
    g = G(len(vertices))
    for a, b in itertools.combinations(vertices, 2):
        if adjacent(a, b):
            g.add(idx[a], idx[b])
    return g


def complete(n): return G(n, itertools.combinations(range(n), 2))
def cycle(n): return G(n, [(i, (i + 1) % n) for i in range(n)])
def path(n): return G(n, [(i, i + 1) for i in range(n - 1)])
def star(k): return G(k + 1, [(0, i) for i in range(1, k + 1)])
def circulant(n, jumps): return G(n, [(i, (i + j) % n) for i in range(n) for j in jumps])


def multipartite(*sizes):
    lab = [p for p, s in enumerate(sizes) for _ in range(s)]
    return from_pairs(list(range(len(lab))), lambda a, b: lab[a] != lab[b])


def wheel(k):
    g = G(k + 1, [(i, (i + 1) % k) for i in range(k)])
    for i in range(k):
        g.add(k, i)
    return g


def cartesian(a, b):
    vs = [(x, y) for x in range(a.n) for y in range(b.n)]
    return from_pairs(vs, lambda p, q: (p[0] == q[0] and q[1] in b.adj[p[1]]) or (p[1] == q[1] and q[0] in a.adj[p[0]]))


def tensor(a, b):
    vs = [(x, y) for x in range(a.n) for y in range(b.n)]
    return from_pairs(vs, lambda p, q: q[0] in a.adj[p[0]] and q[1] in b.adj[p[1]])


def strong(a, b):
    vs = [(x, y) for x in range(a.n) for y in range(b.n)]
    return from_pairs(vs, lambda p, q: (p[0] == q[0] or q[0] in a.adj[p[0]]) and (p[1] == q[1] or q[1] in b.adj[p[1]]))


def disjoint(*gs):
    out, off = G(sum(g.n for g in gs)), 0
    for g in gs:
        for u, v in g.edges():
            out.add(u + off, v + off)
        off += g.n
    return out


def complement(g): return G(g.n, [(u, v) for u, v in itertools.combinations(range(g.n), 2) if v not in g.adj[u]])


def line_graph(g):
    es = g.edges()
    return from_pairs(list(range(len(es))), lambda i, j: len(set(es[i]) & set(es[j])) == 1)


def kneser(n, k):
    return from_pairs(list(itertools.combinations(range(n), k)), lambda a, b: not set(a) & set(b))


def johnson(n, k):
    return from_pairs(list(itertools.combinations(range(n), k)), lambda a, b: len(set(a) & set(b)) == k - 1)


def hypercube(d):
    return from_pairs(list(range(2 ** d)), lambda a, b: bin(a ^ b).count("1") == 1)


def grid(r, c): return cartesian(path(r), path(c))


def mycielski(g):
    n = g.n
    h = G(2 * n + 1, g.edges())
    for u, v in g.edges():
        h.add(u, n + v); h.add(v, n + u)
    for i in range(n):
        h.add(n + i, 2 * n)
    return h


def gen_mycielskian(g, r):
    """mu_r(g): r layers of shadows plus an apex."""
    n = g.n
    h = G(n * (r + 1) + 1, g.edges())
    for layer in range(1, r + 1):
        for u, v in g.edges():
            a, b = (layer - 1) * n, layer * n
            h.add(a + u, b + v); h.add(a + v, b + u)
    for i in range(n):
        h.add(r * n + i, n * (r + 1))
    return h


def gen_petersen(n, k):
    return G(2 * n, [e for i in range(n) for e in ((i, (i + 1) % n), (i, n + i), (n + i, n + (i + k) % n))])


def paley(q):
    sq = {(x * x) % q for x in range(1, q)}
    return from_pairs(list(range(q)), lambda a, b: (a - b) % q in sq)


def friendship(k):
    g = G(2 * k + 1)
    for i in range(k):
        g.add(0, 2 * i + 1); g.add(0, 2 * i + 2); g.add(2 * i + 1, 2 * i + 2)
    return g


def book(k):  # k triangles sharing an edge
    g = G(k + 2, [(0, 1)])
    for i in range(k):
        g.add(0, 2 + i); g.add(1, 2 + i)
    return g


def binary_tree(depth):
    n = 2 ** (depth + 1) - 1
    return G(n, [(i, (i - 1) // 2) for i in range(1, n)])


def apollonian(levels):
    g = complete(4); faces = [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]
    adj = [set(s) for s in g.adj]
    for _ in range(levels):
        new_faces = []
        for a, b, c in faces:
            v = len(adj); adj.append(set())
            for w in (a, b, c):
                adj[v].add(w); adj[w].add(v)
            new_faces += [(a, b, v), (a, c, v), (b, c, v)]
        faces = new_faces
    return G(len(adj), [(u, v) for u in range(len(adj)) for v in adj[u] if u < v])


def from_lists(n, lists):
    return G(n, [(u, v) for u, vs in enumerate(lists) for v in vs])


def platonic():
    ico = G(12, [(0, i) for i in range(1, 6)] + [(i, i % 5 + 1) for i in range(1, 6)]
            + [(i, i + 5) for i in range(1, 6)] + [(i, (i % 5) + 6) for i in range(1, 6)]
            + [(i + 5, (i % 5) + 6) for i in range(1, 6)] + [(11, i + 5) for i in range(1, 6)])
    return {"tetrahedron": complete(4), "cube": hypercube(3), "octahedron": multipartite(2, 2, 2),
            "dodecahedron": gen_petersen(10, 2), "icosahedron": ico}


def chvatal():
    return from_lists(12, [[1, 4, 6, 9], [2, 5, 7], [3, 6, 8], [4, 7, 9], [5, 8], [10, 11], [10, 11], [8, 11], [10], [10, 11]])


def clebsch():  # folded 5-cube: Q4 plus antipodal edges
    g = hypercube(4)
    for v in range(16):
        g.add(v, v ^ 15)
    return g


def shrikhande():
    return from_pairs([(i, j) for i in range(4) for j in range(4)],
                      lambda a, b: ((a[0] - b[0]) % 4, (a[1] - b[1]) % 4) in {(0, 1), (0, 3), (1, 0), (3, 0), (1, 1), (3, 3)})


def heawood(): return G(14, [(i, (i + 1) % 14) for i in range(14)] + [(i, (i + 5) % 14) for i in range(0, 14, 2)])


def robertson():  # (4,5)-cage on 19 vertices
    g = cycle(19)
    chords = [(0, 4), (0, 15), (1, 8), (1, 12), (2, 6), (2, 16), (3, 10), (3, 14), (4, 11), (5, 9), (5, 17),
              (6, 13), (7, 11), (7, 18), (8, 15), (9, 13), (10, 17), (12, 16), (14, 18)]
    for u, v in chords:
        g.add(u, v)
    return g


def mcgee():  # (3,7)-cage, 24 vertices: LCF [12,7,-7]^8
    g = cycle(24)
    lcf = [12, 7, -7] * 8
    for i, j in enumerate(lcf):
        g.add(i, (i + j) % 24)
    return g


def lcf(n, pattern):
    g = cycle(n)
    for i in range(n):
        g.add(i, (i + pattern[i % len(pattern)]) % n)
    return g


def random_graph(n, p, seed):
    r = random.Random(seed)
    return G(n, [(u, v) for u, v in itertools.combinations(range(n), 2) if r.random() < p])


def random_regular(n, d, seed):
    r = random.Random(seed)
    while True:
        stubs = [v for v in range(n) for _ in range(d)]
        r.shuffle(stubs)
        es = {tuple(sorted(stubs[i:i + 2])) for i in range(0, len(stubs), 2)}
        if len(es) == n * d // 2 and all(u != v for u, v in es):
            return G(n, es)


def random_bipartite(a, b, p, seed):
    r = random.Random(seed)
    return G(a + b, [(u, a + v) for u in range(a) for v in range(b) if r.random() < p])


def random_tree(n, seed):
    r = random.Random(seed)
    return G(n, [(i, r.randrange(i)) for i in range(1, n)])


def zoo():
    Z = []
    add = lambda fam, name, g: Z.append((name, fam, g))
    # bipartite families (all hom-equivalent to K2)
    for n in (6, 12): add("Bipartite", f"P{n}", path(n))
    add("Bipartite", "star K1,6", star(6)); add("Bipartite", "binary tree (depth 3)", binary_tree(3))
    add("Bipartite", "random tree (20)", random_tree(20, 1))
    for n in (6, 10, 16): add("Bipartite", f"C{n}", cycle(n))
    add("Bipartite", "grid 3x4", grid(3, 4)); add("Bipartite", "grid 5x5", grid(5, 5))
    for d in (3, 4, 5): add("Bipartite", f"hypercube Q{d}", hypercube(d))
    add("Bipartite", "K3,3", multipartite(3, 3)); add("Bipartite", "K4,6", multipartite(4, 6))
    add("Bipartite", "Heawood", heawood()); add("Bipartite", "Moebius-Kantor GP(8,3)", gen_petersen(8, 3))
    add("Bipartite", "Desargues GP(10,3)", gen_petersen(10, 3)); add("Bipartite", "crown S6", tensor(complete(6), complete(2)))
    add("Bipartite", "random bipartite (10+10)", random_bipartite(10, 10, 0.3, 2))
    # cycles and circulants
    for n in (3, 5, 7, 9, 11, 13, 15, 17, 21): add("Cycles & circulants", f"C{n}", cycle(n))
    for n in (7, 8, 9, 10, 11, 13): add("Cycles & circulants", f"C{n}(1,2)", circulant(n, (1, 2)))
    for n in (8, 10, 11, 14): add("Cycles & circulants", f"C{n}(1,3)", circulant(n, (1, 3)))
    add("Cycles & circulants", "C13(1,5)", circulant(13, (1, 5))); add("Cycles & circulants", "C16(1,3,8)", circulant(16, (1, 3, 8)))
    add("Cycles & circulants", "complement of C7", complement(cycle(7))); add("Cycles & circulants", "complement of C9", complement(cycle(9)))
    add("Cycles & circulants", "Moebius ladder M8 (Wagner)", circulant(8, (1, 4))); add("Cycles & circulants", "Moebius ladder M10", circulant(10, (1, 5)))
    for n in (6, 7, 9): add("Cycles & circulants", f"antiprism ({n})", circulant(2 * n, (1, 2)))
    # cliques, multipartite, near-cliques, unions
    for n in (4, 5, 6, 7): add("Cliques & multipartite", f"K{n}", complete(n))
    add("Cliques & multipartite", "K2,2,2 (octahedron)", multipartite(2, 2, 2))
    add("Cliques & multipartite", "K3,3,3", multipartite(3, 3, 3)); add("Cliques & multipartite", "K2,2,2,2", multipartite(2, 2, 2, 2))
    add("Cliques & multipartite", "K1,2,3,4", multipartite(1, 2, 3, 4)); add("Cliques & multipartite", "Turan T(12,5)", multipartite(3, 3, 2, 2, 2))
    for n in (5, 7):
        g = complete(n); g.adj[0].discard(1); g.adj[1].discard(0)
        add("Cliques & multipartite", f"K{n} minus an edge", g)
    g = complete(6)
    for u, v in ((0, 1), (2, 3), (4, 5)):
        g.adj[u].discard(v); g.adj[v].discard(u)
    add("Cliques & multipartite", "K6 minus a perfect matching", g)
    add("Cliques & multipartite", "2K4", disjoint(complete(4), complete(4)))
    add("Cliques & multipartite", "K4 + C5 (disjoint)", disjoint(complete(4), cycle(5)))
    add("Cliques & multipartite", "K3 + Grotzsch (disjoint)", disjoint(complete(3), mycielski(mycielski(complete(2)))))
    add("Cliques & multipartite", "friendship F4", friendship(4)); add("Cliques & multipartite", "book B5", book(5))
    # planar
    for name, g in platonic().items(): add("Planar", name, g)
    for k in (4, 5, 6, 7, 8, 9): add("Planar", f"wheel W{k}", wheel(k))
    for n in (3, 4, 5, 6, 7): add("Planar", f"prism C{n}xK2", cartesian(cycle(n), complete(2)))
    add("Planar", "Apollonian (2 levels)", apollonian(2))
    tri = from_pairs([(i, j) for i in range(5) for j in range(5 - i)],
                     lambda a, b: (a[0] - b[0], a[1] - b[1]) in {(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)})
    add("Planar", "triangular grid (side 5)", tri)
    # Kneser, Johnson, strongly regular
    for n, k in ((5, 2), (6, 2), (7, 2), (7, 3)): add("Kneser, Johnson, SRG", f"Kneser K({n},{k})", kneser(n, k))
    for n in (5, 6): add("Kneser, Johnson, SRG", f"Johnson J({n},2)", johnson(n, 2))
    add("Kneser, Johnson, SRG", "Clebsch", clebsch()); add("Kneser, Johnson, SRG", "Shrikhande", shrikhande())
    add("Kneser, Johnson, SRG", "rook 3x3 (Paley 9)", cartesian(complete(3), complete(3)))
    add("Kneser, Johnson, SRG", "rook 4x4", cartesian(complete(4), complete(4)))
    add("Kneser, Johnson, SRG", "Paley 13", paley(13)); add("Kneser, Johnson, SRG", "Paley 17", paley(17))
    add("Kneser, Johnson, SRG", "complement of Petersen", complement(kneser(5, 2)))
    # triangle-free, high girth, Mycielski
    m3 = mycielski(complete(2)); m4 = mycielski(m3)
    add("Triangle-free & Mycielski", "Grotzsch (M4)", m4); add("Triangle-free & Mycielski", "Mycielski M5", mycielski(m4))
    add("Triangle-free & Mycielski", "Mycielskian of C7", mycielski(cycle(7)))
    add("Triangle-free & Mycielski", "gen. Mycielskian mu2(C7)", gen_mycielskian(cycle(7), 2))
    add("Triangle-free & Mycielski", "gen. Mycielskian mu3(C9)", gen_mycielskian(cycle(9), 3))
    add("Triangle-free & Mycielski", "Chvatal", chvatal()); add("Triangle-free & Mycielski", "Robertson (4,5)-cage", robertson())
    add("Triangle-free & Mycielski", "McGee (3,7)-cage", mcgee())
    add("Triangle-free & Mycielski", "cubic LCF[5,-5]^12", lcf(24, [5, -5]))
    for n, k in ((7, 2), (9, 2), (11, 3), (12, 5)): add("Triangle-free & Mycielski", f"GP({n},{k})", gen_petersen(n, k))
    add("Triangle-free & Mycielski", "Petersen", kneser(5, 2))
    add("Triangle-free & Mycielski", "C5 x C5 (Cartesian)", cartesian(cycle(5), cycle(5)))
    # random
    for n, p, s in ((12, 0.3, 1), (15, 0.3, 2), (15, 0.5, 3), (20, 0.2, 4), (20, 0.3, 5), (20, 0.5, 6), (25, 0.15, 7), (25, 0.4, 8), (30, 0.1, 9), (30, 0.25, 10)):
        add("Random", f"G({n},{p}) #{s}", random_graph(n, p, s))
    for n, d, s in ((12, 3, 1), (20, 3, 2), (16, 4, 3), (20, 5, 4)):
        add("Random", f"random {d}-regular ({n}) #{s}", random_regular(n, d, s))
    # products and operations
    add("Products & operations", "K3 x K3 (tensor)", tensor(complete(3), complete(3)))
    add("Products & operations", "C5 x K4 (tensor)", tensor(cycle(5), complete(4)))
    add("Products & operations", "K4 x K5 (tensor)", tensor(complete(4), complete(5)))
    add("Products & operations", "C5 strong K2", strong(cycle(5), complete(2)))
    add("Products & operations", "C5 strong C5", strong(cycle(5), cycle(5)))
    add("Products & operations", "K4 x C5 (Cartesian)", cartesian(complete(4), cycle(5)))
    add("Products & operations", "line graph of Petersen", line_graph(kneser(5, 2)))
    add("Products & operations", "line graph of K4,4", line_graph(multipartite(4, 4)))
    add("Products & operations", "line graph of cube", line_graph(hypercube(3)))
    add("Products & operations", "Mycielskian of K4", mycielski(complete(4)))
    add("Products & operations", "complement of C5 x K2", complement(cartesian(cycle(5), complete(2))))
    return Z


# ── invariants ────────────────────────────────────────────────────────────────
def bipartite(g):
    col = [-1] * g.n
    for s in range(g.n):
        if col[s] >= 0:
            continue
        col[s] = 0; q = deque([s])
        while q:
            u = q.popleft()
            for v in g.adj[u]:
                if col[v] < 0:
                    col[v] = 1 - col[u]; q.append(v)
                elif col[v] == col[u]:
                    return False
    return True


def clique_number(g):
    best = 0
    def bk(r, p, x):
        nonlocal best
        if not p and not x:
            best = max(best, r); return
        if r + len(p) <= best:
            return
        u = max(p | x, key=lambda w: len(g.adj[w] & p))
        for v in list(p - g.adj[u]):
            bk(r + 1, p & g.adj[v], x & g.adj[v]); p = p - {v}; x = x | {v}
    bk(0, set(range(g.n)), set())
    return best


def colourable(g, k, limit=2_000_000):
    """Exact k-colourability (DSATUR order). Returns True/False, or None on node limit."""
    col = [-1] * g.n
    nodes = 0
    def pick():
        best, key = -1, None
        for v in range(g.n):
            if col[v] < 0:
                sat = len({col[w] for w in g.adj[v] if col[w] >= 0})
                kk = (sat, len(g.adj[v]))
                if key is None or kk > key:
                    best, key = v, kk
        return best
    def rec(done, used):
        nonlocal nodes
        nodes += 1
        if nodes > limit:
            raise TimeoutError
        if done == g.n:
            return True
        v = pick()
        forb = {col[w] for w in g.adj[v] if col[w] >= 0}
        for c in range(min(k, used + 1)):
            if c not in forb:
                col[v] = c
                if rec(done + 1, max(used, c + 1)):
                    return True
                col[v] = -1
        return False
    try:
        return rec(0, 0)
    except TimeoutError:
        return None


def chromatic(g, lo):
    k = max(lo, 1)
    while k <= g.n:
        r = colourable(g, k)
        if r is None:
            return None
        if r:
            return k
        k += 1


def odd_girth(g):
    best = 10 ** 9
    for s in range(g.n):
        d = {(s, 0): 0}; q = deque([(s, 0)])
        while q:
            u, p = q.popleft()
            for v in g.adj[u]:
                if (v, 1 - p) not in d:
                    d[(v, 1 - p)] = d[(u, p)] + 1; q.append((v, 1 - p))
        best = min(best, d.get((s, 1), 10 ** 9))
    return best if best < 10 ** 9 else 0


def maps_to_cycle(g, c, limit=3_000_000):
    col = [-1] * g.n; nodes = 0
    order = sorted(range(g.n), key=lambda v: -len(g.adj[v]))
    seen, bfs = set(), []
    for s in order:
        if s in seen: continue
        seen.add(s); q = deque([s])
        while q:
            u = q.popleft(); bfs.append(u)
            for v in sorted(g.adj[u], key=lambda w: -len(g.adj[w])):
                if v not in seen: seen.add(v); q.append(v)
    def rec(i):
        nonlocal nodes
        nodes += 1
        if nodes > limit: raise TimeoutError
        if i == g.n: return True
        u = bfs[i]
        for x in range(c):
            if all(col[v] < 0 or (col[v] - x) % c in (1, c - 1) for v in g.adj[u]):
                col[u] = x
                if rec(i + 1): return True
                col[u] = -1
        return False
    try:
        return rec(0)
    except TimeoutError:
        return None


def main():
    rows, lines = [], []
    for name, fam, g in zoo():
        es = g.edges()
        assert g.n <= 128 and es, name
        bip = bipartite(g)
        om = clique_number(g)
        chi = 2 if bip else chromatic(g, om)
        og = 0 if bip else odd_girth(g)
        short = ""
        if bip:
            short = "K2"
        elif chi is not None and chi == om and om <= 8:
            short = f"K{om}"
        elif om == 2 and og in (5, 7, 9, 11) and maps_to_cycle(g, og):
            short = f"C{og}"
        rows.append({"name": name, "family": fam, "n": g.n, "m": len(es), "chi": chi if chi else "",
                     "omega": om, "odd_girth": og if og else "", "shortcut": short})
        lines.append(f"{name}|{fam}|{g.n}|" + ",".join(f"{u}-{v}" for u, v in es))
        print(f"{fam:28s} {name:32s} n={g.n:3d} m={len(es):4d} chi={chi} omega={om} og={og} -> {short or 'compute'}")
    (DATA / "zoo_graphs.txt").write_text("\n".join(lines) + "\n")
    with open(DATA / "zoo_meta.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]))
        w.writeheader(); w.writerows(rows)
    print(len(rows), "graphs;", sum(1 for r in rows if not r["shortcut"]), "need the solver")


if __name__ == "__main__":
    main()
