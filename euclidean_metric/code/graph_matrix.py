"""Build html/graph_matrix.html: graphs on the axes of a metric space.

Views: the distance matrix (graphs on x and y), the distance surface (z = d),
and the triangle cube (graphs on x, y, z; a point marks a triple that breaks
the triangle inequality).

Data sets:
  zoo    the 314 zoo graphs, metric E (profile distance)
  cores  the 85 test cores, metrics E, dist = max(alpha(G,H), alpha(H,G)),
         and d* = shortest-path closure of dist

Usage:  python graph_matrix.py
"""
import csv
import json

import numpy as np
from scipy.cluster.hierarchy import leaves_list, linkage
from scipy.spatial.distance import squareform

import alpha_profile as ap
import zoo_view as zv


def e_matrix(P, w):
    X = P * w
    return np.sqrt(((X[:, None, :] - X[None, :, :]) ** 2).sum(-1))


def profile_metrics(P, w):
    """Metrics that need only the profiles phi(G) (so they work for every graph):
    E      weighted Euclidean distance (the profile metric of the paper)
    E_inf  largest single-test difference max_T |phi_T(G) - phi_T(H)|
    L1     weighted sum of differences
    FJT    Hilbert projective metric on the kept fractions p = 1 - phi (finite-family FJT metric):
           log max_T p_G/p_H + log max_T p_H/p_G; p >= 1/2 always, so it is finite."""
    diff = P[:, None, :] - P[None, :, :]
    q = 1 - P
    ratio = np.log(q[:, None, :]) - np.log(q[None, :, :])
    return {"E": e_matrix(P, w), "E_inf": np.abs(diff).max(-1), "L1": (np.abs(diff) * w).sum(-1),
            "FJT": ratio.max(-1) + (-ratio).max(-1)}


def cluster_order(D):
    Z = linkage(squareform(np.maximum((D + D.T) / 2, 0), checks=False), "average", optimal_ordering=True)
    return leaves_list(Z).tolist()


def violations(D, cap=60000):
    """Triples (i, j, k), i < k, with D[i,k] > D[i,j] + D[j,k]; returns rows (i, j, k, defect).
    D must be unrounded: l1 is exactly tight along every hom chain, so rounding alone creates false violations."""
    n = len(D)
    tol = 1e-9 * max(1.0, float(np.abs(D).max()))
    out = []
    for j in range(n):
        defect = D - D[:, [j]] - D[[j], :]
        ii, kk = np.nonzero(np.triu(defect > tol, 1))
        for i, k in zip(ii, kk):
            if i != j and k != j:
                out.append((int(i), j, int(k), round(float(defect[i, k]), 5)))
    out.sort(key=lambda r: -r[3])
    return out[:cap], len(out)


def orders(names, P, chi, omega, n, D, family=None):
    height = P.sum(1)                                   # ||phi||_1: large = low in the hom order (near K2)
    o = {"height": sorted(range(len(names)), key=lambda i: (height[i], names[i])),
         "chi": sorted(range(len(names)), key=lambda i: (chi[i] or 99, omega[i], n[i], names[i])),
         "cluster": cluster_order(D)}
    if family is not None:
        o["family"] = sorted(range(len(names)), key=lambda i: (family[i], height[i], names[i]))
    return o


def main():
    lab, a, info = ap.load("")
    t_m = info["m"].astype(float)
    cnt = {c: int((info["chi"] == c).sum()) for c in set(info["chi"].tolist())}
    w = np.array([1 / np.sqrt(cnt[c]) for c in info["chi"]])

    # zoo: profiles exactly as in zoo_view (shortcuts + solver)
    meta = list(csv.DictReader(open(ap.DATA / "zoo_meta.csv")))
    comp = {r["target"]: r for r in csv.DictReader(open(ap.DATA / "zoo_profiles_computed.csv"))}
    Pz = []
    for r in meta:
        if r["shortcut"]:
            al = a[:, lab.index(r["shortcut"])]
        else:
            al = np.array([float(comp[r["name"]][t].lstrip("<=")) for t in lab])
        Pz.append(al / t_m)
    Pz = np.array(Pz)
    Ez = e_matrix(Pz, w)
    zn = [r["name"] for r in meta]
    zchi = [int(r["chi"]) if r["chi"] else None for r in meta]
    zom = [int(r["omega"]) for r in meta]
    zfam = [zv.FAMILIES.index(r["family"]) for r in meta]
    zm = profile_metrics(Pz, w)
    zoo = {"names": zn, "chi": zchi, "family": [zv.FAMILIES[f] for f in zfam],
           "metrics": {k: np.round(v, 4).tolist() for k, v in zm.items()},
           "orders": orders(zn, Pz, zchi, zom, [int(r["n"]) for r in meta], Ez, zfam),
           "violations": {}}
    for key in zoo["metrics"]:
        rows, total = violations(zm[key])
        zoo["violations"][key] = {"rows": rows, "total": total}
        print(f"zoo   {key:5s}: {total} violating triples (i<k)")

    # cores: E, dist, d*
    Pc = (a / t_m[:, None]).T
    Ec = e_matrix(Pc, w)
    dist = np.maximum(a, a.T)
    dstar = dist.astype(float).copy()
    for k in range(len(lab)):                           # Floyd-Warshall closure
        dstar = np.minimum(dstar, dstar[:, [k]] + dstar[[k], :])
    omega = [max(int(l[1:]) for l in lab if l[0] == "K" and l[1:].isdigit() and a[lab.index(l), j] == 0)
             for j in range(len(lab))]
    cm = profile_metrics(Pc, w)
    cores = {"names": lab, "chi": info["chi"].tolist(), "family": None,
             "metrics": {**{k: np.round(v, 4).tolist() for k, v in cm.items()},
                         "dist": dist.astype(int).tolist(), "d*": dstar.astype(int).tolist()},
             "orders": orders(lab, Pc, info["chi"].tolist(), omega, info["n"].tolist(), Ec),
             "violations": {}}
    for key in cores["metrics"]:
        rows, total = violations(cm[key] if key in cm else np.array(cores["metrics"][key], dtype=float))
        cores["violations"][key] = {"rows": rows, "total": total}
        print(f"cores {key:5s}: {total} violating triples (i<k)")

    payload = {"sets": {"zoo": zoo, "cores": cores}}
    tpl = (ap.pathlib.Path(__file__).parent / "graph_matrix.tpl").read_text()
    out = ap.HTML / "graph_matrix.html"
    out.write_text(tpl.replace("{{DATA}}", json.dumps(payload, separators=(",", ":"))))
    print("wrote", out, f"{out.stat().st_size / 1e6:.2f} MB")


if __name__ == "__main__":
    main()
