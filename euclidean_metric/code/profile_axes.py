"""Interactive 3D view whose axes are test graphs.

Each axis is one test graph T, and a graph G is placed at its coordinate
phi_T(G) = alpha(T, G) / e(T): the fraction of T's edges that must be deleted
before T maps into G.  The viewer picks the three axis graphs from the 85
test cores; a drawing of each axis graph is shown next to its selector.

Usage:  python profile_axes.py      (writes html/profile_axes_3d.html)
"""
import csv
import json
import pathlib

import numpy as np

import alpha_profile as ap


def graph6_edges(s):
    data = [ord(c) - 63 for c in s.strip()]
    if data[0] == 63:
        n = (data[1] << 12) | (data[2] << 6) | data[3]
        data = data[4:]
    else:
        n = data[0]
        data = data[1:]
    bits = [(x >> (5 - i)) & 1 for x in data for i in range(6)]
    edges, k = [], 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                edges.append([i, j])
            k += 1
    return n, edges


def layout(n, edges):
    """Readable 2D positions in [-1,1]^2: hub in the centre for wheel-like graphs,
    pentagon + pentagram for the Petersen graph, a circle otherwise."""
    import itertools
    import math
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v); adj[v].add(u)
    circ = lambda vs, r, off=0.0: {v: (r * math.sin(2 * math.pi * k / len(vs) + off),
                                       -r * math.cos(2 * math.pi * k / len(vs) + off)) for k, v in enumerate(vs)}
    hubs = [v for v in range(n) if len(adj[v]) == n - 1]
    if n >= 5 and len(hubs) == 1:                     # wheel-like: rim in cycle order if possible
        rim = [v for v in range(n) if v != hubs[0]]
        order = [rim[0]]
        while len(order) < len(rim):
            nxt = [w for w in adj[order[-1]] if w in rim and w not in order]
            if not nxt:
                order = rim; break
            order.append(nxt[0])
        pos = circ(order, 1.0); pos[hubs[0]] = (0.0, 0.0)
        return [pos[v] for v in range(n)]
    if n == 10 and len(edges) == 15 and all(len(a) == 3 for a in adj):   # Petersen-like cubic graph
        for c in itertools.permutations(range(n), 5):
            if c[0] == min(c) and all(c[(i + 1) % 5] in adj[c[i]] for i in range(5)):
                inner = [next(iter(adj[v] - set(c))) for v in c]
                if len(set(inner)) == 5:
                    pos = {**circ(list(c), 1.0), **circ(inner, 0.5)}
                    return [pos[v] for v in range(n)]
    return [circ(list(range(n)), 1.0)[v] for v in range(n)]


def main():
    lab, a, info = ap.load("")
    meta = {r["label"]: r for r in csv.DictReader(open(ap.DATA / "cores_meta.csv"))}
    t_m = info["m"].astype(float)
    tests = []
    for t, l in enumerate(lab):
        n, edges = graph6_edges(meta[l]["graph6"])
        assert len(edges) == info["m"][t]
        tests.append({"label": l, "n": n, "m": int(info["m"][t]), "chi": int(info["chi"][t]),
                      "named": ap.is_named(l), "edges": edges,
                      "pos": [[round(x, 4), round(y, 4)] for x, y in layout(n, edges)]})

    def prof(alpha_cols):                       # rows = tests -> graphs x tests
        return np.round(alpha_cols / t_m[:, None], 5).T.tolist()

    lab9, a9, info9 = ap.load("_n9")
    idx = [lab9.index(t) for t in lab]
    sets = {}
    for key, (L, A, inf) in {"n8": (lab, a, info), "n9": (lab9, a9[idx, :], info9)}.items():
        sets[key] = {"label": L, "chi": inf["chi"].tolist(), "n": inf["n"].tolist(), "m": inf["m"].tolist(),
                     "clique": [ap.is_clique(l) for l in L], "named": [ap.is_named(l) for l in L], "P": prof(A)}
    gp = list(csv.DictReader(open(ap.DATA / "gp_profiles.csv")))
    cc = sorted(csv.DictReader(open(ap.DATA / "circular_profiles.csv")), key=lambda r: int(r["p"]) / int(r["q"]))
    extra = {
        "gp": {"label": [ap.gp_label(r["target"]) for r in gp],
               "P": prof(np.array([[float(r[t]) for t in lab] for r in gp]).T)},
        "circ": {"label": [f"K{r['p']}" if r["q"] == "1" else f"K{r['p']}/{r['q']}" for r in cc],
                 "q": [int(r["q"]) for r in cc],
                 "chi": [-(-int(r["p"]) // int(r["q"])) for r in cc],
                 "P": prof(np.array([[float(r[t]) for t in lab] for r in cc]).T)},
    }
    cnt = {c: int((info["chi"] == c).sum()) for c in set(info["chi"].tolist())}
    w = [round(1 / cnt[int(c)] ** 0.5, 6) for c in info["chi"]]         # chi-balanced test weights
    payload = {"tests": tests, "sets": sets, **extra, "w": w, "default": ["K5", "Petersen", "W5"]}
    tpl = (pathlib.Path(__file__).parent / "profile_axes_3d.tpl").read_text()
    html = (tpl.replace("{{DATA}}", json.dumps(payload, separators=(",", ":")))
               .replace("{{SLOTS}}", json.dumps(ap.SLOTS)).replace("{{SLOTS_DARK}}", json.dumps(ap.SLOTS_DARK)))
    out = ap.HTML / "profile_axes_3d.html"
    out.write_text(html)
    print("wrote", out, f"{out.stat().st_size / 1e6:.2f} MB")


if __name__ == "__main__":
    main()
