"""Agent R: what the Euclidean alpha-profile space lets us see/do.
Usage: python R_analysis.py  (reads repo data, writes R_*.png + prints numbers)"""
import csv, itertools, pathlib, sys
import numpy as np
from scipy.optimize import linprog
from scipy.cluster.hierarchy import linkage, fcluster, dendrogram
from scipy.stats import spearmanr
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

DATA = pathlib.Path("/home/rostam/kara/NonHomomorphism/open_problems/metric_space/data")
OUT = pathlib.Path(__file__).parent
NAMED = {"Petersen", "Grotzsch", "Icosahedron", "W5", "W7"}
def is_named(l): return (l[0] in "KCW" and l[1:].isdigit()) or l in NAMED

def g6(s):
    b = [ord(c) - 63 for c in s]; n = b[0]; bits = []
    for x in b[1:]: bits += [(x >> (5 - i)) & 1 for i in range(6)]
    A = np.zeros((n, n), int); k = 0
    for j in range(1, n):
        for i in range(j):
            A[i, j] = A[j, i] = bits[k]; k += 1
    return A

def invariants(A):
    n = len(A); nb = [int(sum(1 << j for j in range(n) if A[i, j])) for i in range(n)]
    # independent sets (bitmask) -> omega via complement cliques, chi_f via LP
    def indep(S): return all(not (nb[i] & S) for i in range(n) if S >> i & 1)
    ind = [S for S in range(1, 1 << n) if indep(S)]
    maxind = [S for S in ind if not any((S | (1 << v)) in set_ind for v in range(n) if not S >> v & 1)] if False else None
    set_ind = set(ind)
    maxind = [S for S in ind if all(((S | 1 << v) not in set_ind) for v in range(n) if not S >> v & 1)]
    M = np.array([[S >> v & 1 for S in maxind] for v in range(n)], float)
    r = linprog(np.ones(len(maxind)), A_ub=-M, b_ub=-np.ones(n), bounds=(0, None), method="highs")
    chif = r.fun
    # omega
    om = 1
    def ext(C, cand, size):
        nonlocal om
        om = max(om, size)
        while cand:
            v = cand.bit_length() - 1; cand &= ~(1 << v)
            if size + bin(cand).count("1") + 1 > om: ext(C | 1 << v, cand & nb[v], size + 1)
    ext(0, (1 << n) - 1, 0)
    # odd girth via bipartite double cover BFS
    og = 10 ** 9
    for s in range(n):
        dist = {(s, 0): 0}; fr = [(s, 0)]
        while fr:
            nf = []
            for (u, p) in fr:
                for w in range(n):
                    if A[u, w] and (w, 1 - p) not in dist:
                        dist[(w, 1 - p)] = dist[(u, p)] + 1; nf.append((w, 1 - p))
            fr = nf
        if (s, 1) in dist: og = min(og, dist[(s, 1)])
    m = A.sum() // 2; deg = A.sum(1)
    tri = np.trace(A @ A @ A) / 6
    return dict(n=n, m=m, dens=2 * m / (n * (n - 1)), omega=om, oddg=og, chif=chif,
                maxdeg=deg.max(), avgdeg=deg.mean(), tri_per_edge=tri / m, alpha_ind=bin(max(ind, key=lambda S: bin(S).count('1'))).count('1'))

def load(sfx):
    rows = list(csv.reader(open(DATA / f"alpha{sfx}.csv")))
    lab = rows[0][1:]
    a = np.array([[float(x) for x in r[1:]] for r in rows[1:]])
    meta = {r["label"]: r for r in csv.DictReader(open(DATA / f"cores_meta{sfx}.csv"))}
    m = np.array([int(meta[l]["m"]) for l in lab]); chi = np.array([int(meta[l]["chi"]) for l in lab])
    X = (a / m[:, None]).T
    return lab, X, chi, [meta[l]["graph6"] for l in lab]

def pca(X):
    mu = X.mean(0); U, S, Vt = np.linalg.svd(X - mu, full_matrices=False)
    return (X - mu) @ Vt.T, S ** 2 / (S ** 2).sum(), Vt, mu

def in_hull_of_others(X, i):
    others = np.delete(X, i, 0); k = len(others)
    Aeq = np.vstack([others.T, np.ones(k)]); beq = np.append(X[i], 1)
    r = linprog(np.zeros(k), A_eq=Aeq, b_eq=beq, bounds=(0, None), method="highs")
    return r.status == 0

def main():
    lab, X, chi, gs = load("")
    N = len(lab); I = lab.index
    inv = [invariants(g6(s)) for s in gs]
    keys = ["chi", "omega", "chif", "oddg", "dens", "n", "m", "avgdeg", "tri_per_edge"]
    V = {k: np.array([v[k] for v in inv], float) for k in keys if k != "chi"}; V["chi"] = chi.astype(float)
    V["oddg"] = np.where(V["oddg"] == 3, 3, V["oddg"])
    V["trifree"] = (V["omega"] == 2).astype(float)
    keys = ["trifree"] + keys
    print("named invariants:", [(l, inv[k]["omega"], inv[k]["oddg"], round(inv[k]["chif"], 3)) for k, l in enumerate(lab) if is_named(l)])

    Y, var, Vt, mu = pca(X)
    print("\n== 1. PCA on all 85 ==  var:", np.round(var[:6], 3))
    def pc_report(Y, Vt, var, mask, title, npc=5):
        print(f"--- {title}")
        for p in range(npc):
            cors = {k: np.corrcoef(Y[:, p], V[k][mask])[0, 1] if V[k][mask].std() > 0 else np.nan for k in keys}
            best = sorted(cors.items(), key=lambda kv: -abs(np.nan_to_num(kv[1])))[:4]
            top = np.argsort(-np.abs(Vt[p]))[:5]
            ext = np.argsort(Y[:, p]); L = np.array(lab)[mask]
            print(f"PC{p+1} {var[p]:.1%} | r: " + ", ".join(f"{k}={c:+.2f}" for k, c in best)
                  + " | tests: " + ", ".join(f"{lab[t]}({Vt[p, t]:+.2f})" for t in top)
                  + f" | low: {list(L[ext[:3]])} high: {list(L[ext[-3:]])}")
    pc_report(Y, Vt, var, np.ones(N, bool), "all cores")
    # 1b. remove triangle effect: PCA within omega>=3 and within triangle-free
    for name, mask in [("omega>=3", V["omega"] >= 3), ("triangle-free", V["omega"] == 2)]:
        Ys, vs, Vts, _ = pca(X[mask])
        pc_report(Ys, Vts, vs, mask, f"within {name} ({mask.sum()} cores), var {np.round(vs[:4],3)}", npc=min(4, mask.sum() - 1))
    # chi-balanced weights: each chi class weight 1 in the covariance
    w = np.array([1 / (chi == c).sum() for c in chi]); w /= w.sum()
    mu_w = (w[:, None] * X).sum(0); Xw = (X - mu_w) * np.sqrt(w)[:, None]
    _, Sw, Vtw = np.linalg.svd(Xw, full_matrices=False); Yw = (X - mu_w) @ Vtw.T; vw = Sw ** 2 / (Sw ** 2).sum()
    pc_report(Yw, Vtw, vw, np.ones(N, bool), f"chi-balanced weights, var {np.round(vw[:4],3)}", npc=3)
    # residual after regressing out the omega-indicator block
    Z = np.column_stack([np.ones(N)] + [(V["omega"] == k).astype(float) for k in sorted(set(V["omega"]))[1:]])
    R = X - Z @ np.linalg.lstsq(Z, X, rcond=None)[0]
    Yr, vr, Vtr, _ = pca(R + 0)
    pc_report(Yr, Vtr, vr, np.ones(N, bool), f"after regressing out omega-class means, var {np.round(vr[:4],3)}", npc=3)

    # ---- 2. clustering
    print("\n== 2. Ward clustering ==")
    Lk = linkage(X, "ward")
    for k in (2, 3, 4, 5, 6, 8):
        cl = fcluster(Lk, k, "maxclust")
        desc = []
        for c in sorted(set(cl)):
            s = cl == c
            desc.append(f"[{s.sum()}: chi{sorted(set(chi[s]))} om{sorted(set(V['omega'][s].astype(int)))} "
                        + ",".join(l for l, t in zip(lab, s) if t and is_named(l)) + "]")
        print(f"k={k}: " + " ".join(desc))
    D = np.sqrt(((X[:, None] - X[None]) ** 2).sum(-1))
    nn = np.sort(D, 1)[:, 1]
    o = np.argsort(-nn)[:10]
    print("most isolated (NN distance):", [(lab[i], round(nn[i], 3)) for i in o])
    print("median NN dist", np.median(nn))
    # same-chi vs NN: fraction whose nearest neighbour has same chi / omega
    nnidx = np.argsort(D, 1)[:, 1]
    print("NN same chi: %.2f, same omega: %.2f" % ((chi[nnidx] == chi).mean(), (V["omega"][nnidx] == V["omega"]).mean()))

    # ---- 3a. centroids
    print("\n== 3a. chi-class centroids ==")
    cents = {}
    for c in sorted(set(chi)):
        s = chi == c; cen = X[s].mean(0); cents[c] = cen
        d = np.linalg.norm(X - cen, axis=1); j = np.argsort(d)[:3]
        print(f"chi={c} ({s.sum()}): nearest {[(lab[x], round(d[x], 3)) for x in j]}, spread(mean dist)={d[s].mean():.3f}")
    for c in sorted(set(V["omega"].astype(int))):
        s = V["omega"] == c; cen = X[s].mean(0); d = np.linalg.norm(X - cen, axis=1); j = np.argsort(d)[:3]
        print(f"omega={c} ({s.sum()}): nearest {[(lab[x], round(d[x], 3)) for x in j]}")
    # is the centroid realised? does a 'K_{3.5}' exist: midpoint of K3,K4
    # ---- 3b. segment K3-K4 and others
    print("\n== 3b. segments ==")
    segs = {}
    for a_, b_ in [("K3", "K4"), ("K2", "K3"), ("K4", "K5"), ("C5", "K3"), ("K2", "C5")]:
        p, q = X[I(a_)], X[I(b_)]; dv = q - p
        t = np.clip((X - p) @ dv / (dv @ dv), 0, 1); dist = np.linalg.norm(X - (p + t[:, None] * dv), axis=1)
        segs[(a_, b_)] = (t, dist)
        j = [x for x in np.argsort(dist) if lab[x] not in (a_, b_)][:6]
        print(f"{a_}-{b_} (len {np.linalg.norm(dv):.3f}): " + ", ".join(f"{lab[x]}(t={t[x]:.2f},d={dist[x]:.3f})" for x in j))
    # betweenness: E(a,x)+E(x,b) - E(a,b) small => metric betweenness
    for a_, b_ in [("K3", "K4"), ("K2", "K3")]:
        ex = D[I(a_)] + D[I(b_)] - D[I(a_), I(b_)]
        j = [x for x in np.argsort(ex) if lab[x] not in (a_, b_)][:5]
        print(f"metric-between {a_},{b_}: " + ", ".join(f"{lab[x]}({ex[x]:.3f})" for x in j))
    # ---- 3c. extreme points
    print("\n== 3c. convex hull extreme points (full space) ==")
    extreme = [i for i in range(N) if not in_hull_of_others(X, i)]
    print(f"{len(extreme)}/{N} extreme:", [lab[i] for i in extreme])
    nonext = [lab[i] for i in range(N) if i not in extreme]
    print("non-extreme:", nonext)
    from scipy.spatial import ConvexHull
    for d in (2, 3):
        h = ConvexHull(Y[:, :d]); print(f"hull vertices in PC1..{d}:", [lab[i] for i in h.vertices])
    # ---- 3d. regression
    print("\n== 3d. regression ==")
    def r2(Z, Yt):
        B = np.linalg.lstsq(Z, Yt, rcond=None)[0]; res = Yt - Z @ B
        return 1 - (res ** 2).sum() / ((Yt - Yt.mean(0)) ** 2).sum()
    one = np.ones((N, 1))
    def onehot(v): return np.column_stack([(v == k).astype(float) for k in sorted(set(v))[1:]])
    for name, Z in [("chi linear", np.column_stack([one, V["chi"]])), ("omega linear", np.column_stack([one, V["omega"]])),
                    ("chi one-hot", np.column_stack([one, onehot(V["chi"])])), ("omega one-hot", np.column_stack([one, onehot(V["omega"])])),
                    ("chi+omega one-hot", np.column_stack([one, onehot(V["chi"]), onehot(V["omega"])])),
                    ("omega one-hot + oddg one-hot", np.column_stack([one, onehot(V["omega"]), onehot(V["oddg"])])),
                    ("chi,omega,oddg,chif one-hot/lin", np.column_stack([one, onehot(V["chi"]), onehot(V["omega"]), onehot(V["oddg"]), V["chif"]]))]:
        print(f"  phi ~ {name}: R^2 = {r2(Z, X):.3f}")
    # converse: predict chi from phi. LOO ridge over the 85; and in n9 with restricted features
    def loo_ridge(F, y, lam):
        n_ = len(y); F1 = np.column_stack([np.ones(n_), F]); P = np.eye(F1.shape[1]); P[0, 0] = 0
        H = F1 @ np.linalg.solve(F1.T @ F1 + lam * P, F1.T); yh = H @ y
        return (y - yh) / (1 - np.diag(H)), yh
    for tgt in ("chi", "omega", "chif"):
        y = V[tgt]
        best = min(((np.mean(loo_ridge(X, y, lam)[0] ** 2), lam) for lam in 10.0 ** np.arange(-6, 2)))
        e, yh = loo_ridge(X, y, best[1]); pred = y - e
        print(f"  {tgt} ~ linear(phi), 85 cores: LOO RMSE {np.sqrt(best[0]):.3f} (lam {best[1]:g}), rounded LOO exact {np.mean(np.round(pred) == y):.2f}")
    # exact linear separability of chi<=k by phi? (LP feasibility with margin)
    for k in (2, 3, 4):
        s = np.where(chi <= k, 1, -1)
        Aub = -s[:, None] * np.column_stack([X, np.ones(N)]); r = linprog(np.zeros(X.shape[1] + 1), A_ub=Aub, b_ub=-np.ones(N), bounds=(None, None), method="highs")
        print(f"  {{chi<={k}}} linearly separable in phi-space: {r.status == 0}")
    # PCA-only (low-dim) prediction
    for d in (2, 3, 5, 10):
        e, _ = loo_ridge(Y[:, :d], V["chi"], 1e-6)
        print(f"  chi ~ PC1..{d}: LOO RMSE {np.sqrt(np.mean(e**2)):.3f}, rounded exact {np.mean(np.round(V['chi']-e)==V['chi']):.2f}")

    # ---- n9 robustness
    lab9, X9, chi9, gs9 = load("_n9"); N9 = len(lab9)
    Y9, var9, Vt9, _ = pca(X9)
    print("\n== n9 set ==  var:", np.round(var9[:6], 3))
    inv9 = [invariants(g6(s)) for s in gs9]
    om9 = np.array([v["omega"] for v in inv9], float); og9 = np.array([v["oddg"] for v in inv9], float)
    cf9 = np.array([v["chif"] for v in inv9]); de9 = np.array([v["dens"] for v in inv9]); n9 = np.array([v["n"] for v in inv9], float)
    tp9 = np.array([v["tri_per_edge"] for v in inv9])
    print("omega dist", {int(k): int((om9 == k).sum()) for k in set(om9)})
    for p in range(5):
        cs = {k: np.corrcoef(Y9[:, p], v)[0, 1] for k, v in dict(trifree=(om9 == 2) * 1.0, chi=chi9 * 1.0, omega=om9, chif=cf9, oddg=og9, dens=de9, n=n9, tri_per_edge=tp9).items()}
        top = np.argsort(-np.abs(Vt9[p]))[:4]
        print(f"PC{p+1} {var9[p]:.1%}: " + ", ".join(f"{k}={c:+.2f}" for k, c in sorted(cs.items(), key=lambda kv: -abs(kv[1]))[:4])
              + " | tests " + ", ".join(f"{lab9[t]}({Vt9[p,t]:+.2f})" for t in top))
    # predict chi from phi with only the 85 test columns (features << samples)
    cols = [lab9.index(l) for l in lab]
    F = X9[:, cols]
    for tgt, y in (("chi", chi9 * 1.0), ("omega", om9), ("chif", cf9)):
        best = min(((np.mean(loo_ridge(F, y, lam)[0] ** 2), lam) for lam in 10.0 ** np.arange(-6, 2)))
        e, _ = loo_ridge(F, y, best[1])
        print(f"  n9: {tgt} ~ linear(phi restricted to 85 tests): LOO RMSE {np.sqrt(best[0]):.3f}, rounded exact {np.mean(np.round(y - e) == y):.3f}")
    # chi confusions
    e, _ = loo_ridge(F, chi9 * 1.0, 1e-3); pr = np.round(chi9 - e)
    bad = np.where(pr != chi9)[0]
    print("  misclassified chi:", [(lab9[i], int(chi9[i]), int(pr[i])) for i in bad[:15]])
    Lk9 = linkage(X9, "ward")
    for k in (2, 4, 6):
        cl = fcluster(Lk9, k, "maxclust")
        print(f"  n9 Ward k={k}: " + " ".join(f"[{(cl==c).sum()}: chi{dict(zip(*np.unique(chi9[cl==c], return_counts=True)))} om{dict(zip(*np.unique(om9[cl==c].astype(int), return_counts=True)))}]" for c in sorted(set(cl))))
    ext9 = []  # extreme points among n9 in PC space (full LP expensive: use top-10 PCs)
    for i in range(N9):
        if not in_hull_of_others(Y9[:, :10], i): ext9.append(i)
    print(f"  n9 extreme pts in PC1..10: {len(ext9)}; named among them:", [lab9[i] for i in ext9 if is_named(lab9[i])])

    np.savez(OUT / "R_cache.npz", X=X, Y=Y, var=var, chi=chi, omega=V["omega"], oddg=V["oddg"], chif=V["chif"],
             lab=np.array(lab), extreme=np.array(extreme), Y9=Y9[:, :4], var9=var9[:4], chi9=chi9, om9=om9, lab9=np.array(lab9),
             t34=segs[("K3", "K4")][0], d34=segs[("K3", "K4")][1], Yw=Yw[:, :3], vw=vw[:3], Yr=Yr[:, :3], vr=vr[:3])
    return locals()

if __name__ == "__main__":
    main()
