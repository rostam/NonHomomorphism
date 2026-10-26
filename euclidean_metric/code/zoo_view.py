"""Build html/graph_zoo_3d.html: a varied zoo of graphs (mostly non-cores) in the
Euclidean profile space.

Profiles come from data/zoo_meta.csv (exact shortcuts: bipartite -> K2,
chi = omega = k -> K_k, maps onto its shortest odd cycle C_g -> C_g) and
data/zoo_profiles_computed.csv (Rust solver; entries '<=v' are upper bounds
after a timeout).

Usage:  python zoo_view.py
"""
import csv
import json

import numpy as np

import alpha_profile as ap
import profile_axes as pa

FAMILIES = ["Bipartite", "Cycles & circulants", "Cliques & multipartite", "Planar",
            "Kneser, Johnson, SRG", "Triangle-free & Mycielski", "Random", "Products & operations"]


def main():
    lab, a, info = ap.load("")
    t_m = info["m"].astype(float)
    meta = list(csv.DictReader(open(ap.DATA / "zoo_meta.csv")))
    comp = {r["target"]: r for r in csv.DictReader(open(ap.DATA / "zoo_profiles_computed.csv"))}
    core_alpha = {l: a[:, j] for j, l in enumerate(lab)}           # alpha(T, core) for every test T
    rows = []
    for r in meta:
        if r["shortcut"]:
            al, exact, how = core_alpha[r["shortcut"]], True, f"shortcut ≡ {r['shortcut']}"
        else:
            c = comp[r["name"]]
            al = np.array([float(c[t].lstrip("<=")) for t in lab])
            # The icosahedron has 20 triangles and every edge lies in exactly 2 of them, so mapping it
            # into a triangle-free graph deletes >= 10 edges: an upper bound of 10 is then exact.
            bounds_ok = all(not c[t].startswith("<=") or (t == "Icosahedron" and c[t] == "<=10" and r["omega"] == "2")
                            for t in lab)
            exact = c["exact_all"] == "true" or bounds_ok
            how = "computed" if exact else "computed (some entries are upper bounds)"
        rows.append((r, al / t_m, exact, how))

    # same PCA axes as alpha_profile.py
    cnt = {}
    for c in info["chi"]:
        cnt[c] = cnt.get(c, 0) + 1
    w = np.array([1 / np.sqrt(cnt[c]) for c in info["chi"]])
    X = (a / t_m[:, None]).T * w
    mu = X.mean(0)
    _, S, Vt = np.linalg.svd(X - mu, full_matrices=False)
    var = S ** 2 / (S ** 2).sum()
    proj = lambda Z: (Z * w - mu) @ Vt[:3].T
    core_raw = (a / t_m[:, None]).T

    zoo = {"name": [], "family": [], "n": [], "m": [], "chi": [], "omega": [], "og": [], "how": [], "exact": [],
           "at": [], "P": [], "pc": []}
    for r, prof, exact, how in rows:
        d = np.abs(core_raw - prof).max(1)
        j = int(d.argmin())
        zoo["name"].append(r["name"]); zoo["family"].append(FAMILIES.index(r["family"]))
        zoo["n"].append(int(r["n"])); zoo["m"].append(int(r["m"]))
        zoo["chi"].append(int(r["chi"]) if r["chi"] else None); zoo["omega"].append(int(r["omega"]))
        zoo["og"].append(int(r["odd_girth"]) if r["odd_girth"] else None)
        zoo["how"].append(how); zoo["exact"].append(exact)
        zoo["at"].append(lab[j] if d[j] < 1e-9 else "")
        zoo["P"].append(np.round(prof, 5).tolist())
        zoo["pc"].append(np.round(proj(prof[None, :])[0], 5).tolist())
    cores = {"label": lab, "chi": info["chi"].tolist(), "clique": [ap.is_clique(l) for l in lab],
             "named": [ap.is_named(l) for l in lab], "P": np.round(core_raw, 5).tolist(),
             "pc": np.round(proj(core_raw), 5).tolist()}
    tests = []
    gmeta = {r["label"]: r for r in csv.DictReader(open(ap.DATA / "cores_meta.csv"))}
    for t, l in enumerate(lab):
        n, edges = pa.graph6_edges(gmeta[l]["graph6"])
        tests.append({"label": l, "n": n, "m": int(info["m"][t]), "chi": int(info["chi"][t]), "named": ap.is_named(l),
                      "edges": edges, "pos": [[round(x, 4), round(y, 4)] for x, y in pa.layout(n, edges)]})
    payload = {"families": FAMILIES, "zoo": zoo, "cores": cores, "tests": tests,
               "var": [round(float(v), 4) for v in var[:3]], "default": ["K5", "Petersen", "W5"]}
    tpl = (ap.pathlib.Path(__file__).parent / "graph_zoo_3d.tpl").read_text()
    html = (tpl.replace("{{DATA}}", json.dumps(payload, separators=(",", ":")))
               .replace("{{SLOTS}}", json.dumps(ap.SLOTS)).replace("{{SLOTS_DARK}}", json.dumps(ap.SLOTS_DARK)))
    out = ap.HTML / "graph_zoo_3d.html"
    out.write_text(html)
    n_own = sum(1 for x in zoo["at"] if not x)
    print("wrote", out, f"{out.stat().st_size / 1e6:.2f} MB;", len(rows), "graphs,", n_own, "on a point of their own,",
          sum(not e for e in zoo["exact"]), "with upper-bound entries")


if __name__ == "__main__":
    main()
