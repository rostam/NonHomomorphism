"""Agent Q, task 1+3: test-family design and stability for the alpha-profile metric E."""
import csv, pathlib, sys
import numpy as np
from scipy.stats import spearmanr, rankdata

REPO = pathlib.Path("/home/rostam/kara/NonHomomorphism/open_problems/metric_space/data")
DISC = pathlib.Path(__file__).parent.parent / "discussion"
rng = np.random.default_rng(0)


def mat(path):
    rows = list(csv.reader(open(path)))
    return rows[0][1:], np.array([[float(x) for x in r[1:]] for r in rows[1:]])


def load(suf):
    lab, a = mat(REPO / f"alpha{suf}.csv")
    meta = {r["label"]: r for r in csv.DictReader(open(REPO / f"cores_meta{suf}.csv"))}
    m = np.array([int(meta[l]["m"]) for l in lab]); n = np.array([int(meta[l]["n"]) for l in lab])
    chi = np.array([int(meta[l]["chi"]) for l in lab])
    s = "" if suf == "" else suf
    l2, dist = mat(DISC / f"dist{s}.csv"); assert l2 == lab
    l3, dstar = mat(DISC / f"dist_closure{s}.csv"); assert l3 == lab
    l4, dn = mat(DISC / f"dnorm{s}.csv"); assert l4 == lab
    return lab, a, m, n, chi, dist, dstar, dn


BASIS = ["K2", "K3", "K4", "K5", "K6", "C5", "C7", "C9", "Petersen", "Grotzsch", "W5", "Icosahedron"]


def Emat(X, w=None):
    Y = X if w is None else X * w[None, :]
    sq = (Y ** 2).sum(1)
    D2 = np.maximum(sq[:, None] + sq[None, :] - 2 * Y @ Y.T, 0)
    return np.sqrt(D2)


def dims(X, w=None):
    Y = X if w is None else X * w[None, :]
    Yc = Y - Y.mean(0)
    s = np.linalg.svd(Yc, compute_uv=False)
    lam = s ** 2
    rank = int((s > 1e-9 * s[0]).sum())
    pr = lam.sum() ** 2 / (lam ** 2).sum()
    cum = np.cumsum(lam) / lam.sum()
    return rank, pr, lam[0] / lam.sum(), int(np.searchsorted(cum, 0.9) + 1), int(np.searchsorted(cum, 0.99) + 1)


def report(name, X, w, iu, refs, out):
    E = Emat(X, w)
    e = E[iu]
    rank, pr, pc1, k90, k99 = dims(X, w)
    zero = int((e < 1e-12).sum())
    nclass = len({tuple(np.round(r, 9)) for r in X})
    row = [name, X.shape[1], rank, f"{pr:.2f}", f"{pc1:.0%}", k90, k99]
    for rn, R in refs:
        r = R[iu]
        row.append(f"{np.corrcoef(e, r)[0,1]:.3f}/{spearmanr(e, r)[0]:.3f}")
    row += [zero, nclass]
    out.append(row)
    return E


def greedy_sep(A, cand, names):
    """A[:, t] = raw alpha(t, G) for targets G (rows). Greedy partition refinement."""
    N = A.shape[0]
    lab = np.zeros(N, dtype=np.int64)
    chosen = []
    def pairs_same(l):
        _, c = np.unique(l, return_counts=True)
        return int((c * (c - 1) // 2).sum())
    while pairs_same(lab) > 0:
        best = None
        for t in cand:
            if t in chosen: continue
            _, nl = np.unique(np.stack([lab, A[:, t].astype(np.int64)], 1), axis=0, return_inverse=True)
            p = pairs_same(nl.ravel())
            if best is None or p < best[0]:
                best = (p, t, nl.ravel())
        if best is None or best[0] == pairs_same(lab):
            return chosen, pairs_same(lab), False
        chosen.append(best[1]); lab = best[2]
    return chosen, 0, True


def main():
    out_lines = []
    P = lambda *s: (print(*s), out_lines.append(" ".join(str(x) for x in s)))
    for suf, tag in [("", "n8 (85 cores)"), ("_n9", "n9 (1276 cores)")]:
        lab, a, m, n, chi, dist, dstar, dn = load(suf)
        N = len(lab); iu = np.triu_indices(N, 1)
        X = (a / m[:, None]).T  # rows = targets G, cols = tests T
        idx = {l: i for i, l in enumerate(lab)}
        B = [idx[b] for b in BASIS]
        all_t = np.arange(N)
        refs = [("dist", dist), ("d*", dstar), ("d_n", dn)]
        # chi-balanced weights: each chi class of tests gets total squared weight 1
        def chiw(cols):
            w = np.zeros(len(cols))
            for k, t in enumerate(cols):
                w[k] = 1 / np.sqrt((chi[cols] == chi[t]).sum())
            return w
        tf_tests = [t for t in all_t if a[t, idx["K2"]] >= 0 and a[t, idx["C5"]] == 0 or False]
        rows = []
        fams = {
            "all tests": (all_t, None),
            "all, chi-balanced": (all_t, chiw(all_t)),
            "basis B12": (np.array(B), None),
            "basis B12, chi-balanced": (np.array(B), chiw(np.array(B))),
            "triangle-free tests only": (np.array([t for t in all_t if a[idx["K3"], t] > 0]), None),
        }
        Es = {}
        for name, (cols, w) in fams.items():
            Es[name] = report(name, X[:, cols], w, iu, refs, rows)
        P(f"\n### {tag}: profile-matrix dimension and correlation of E with dist / d* / d_n (Pearson/Spearman)\n")
        P("| family | #tests | rank | eff.dim (PR) | PC1 | #PC 90% | #PC 99% | E~dist | E~d* | E~d_n | #pairs E=0 | #distinct profiles |")
        P("|---|---|---|---|---|---|---|---|---|---|---|---|")
        for r in rows:
            P("| " + " | ".join(str(x) for x in r) + " |")
        P(f"\ntriangle-free tests (alpha(K3,T)>0): {len(fams['triangle-free tests only'][0])}; chi of tests: "
          + ", ".join(f"chi={c}:{(chi==c).sum()}" for c in sorted(set(chi))))
        # greedy separation
        A = a.T  # rows G, cols T: alpha(T, G)
        P(f"\n### {tag}: greedy separating test sets (raw alpha values, all {N} cores as targets)\n")
        P("| candidate tests | greedy size | separates all? | chosen tests |")
        P("|---|---|---|---|")
        for cname, cand in [("all cores", list(all_t)), ("basis B12 only", B)] + \
                [(f"tests with n<={k}", [t for t in all_t if n[t] <= k]) for k in (5, 6, 7, 8)] + \
                [("non-complete tests", [t for t in all_t if not (lab[t][0] == 'K' and lab[t][1:].isdigit())])]:
            ch, left, ok = greedy_sep(A, cand, lab)
            P(f"| {cname} ({len(cand)}) | {len(ch)} | {'yes' if ok else f'no, {left} pairs merged'} | {', '.join(lab[t] for t in ch)} |")
        vmax = max(len(np.unique(A[:, t])) for t in all_t)
        P(f"\ninformation lower bound: max #distinct values of one test = {vmax} -> need >= {int(np.ceil(np.log(N)/np.log(vmax)))} tests")
        # basis + greedy completion
        ch, left, ok = greedy_sep(A, list(all_t), lab)
        # stability
        P(f"\n### {tag}: stability of E (Spearman rho between E_F and E_F±T over all pairs)\n")
        P("| family F | operation | #variants | min rho | median rho | most disruptive T |")
        P("|---|---|---|---|---|---|")
        def stab(cols, ops, label):
            base = Emat(X[:, cols])[iu]; rb = rankdata(base)
            res = []
            for t in ops:
                if label == "remove":
                    c2 = np.array([c for c in cols if c != t])
                else:
                    c2 = np.append(cols, t)
                e2 = Emat(X[:, c2])[iu]
                res.append((np.corrcoef(rb, rankdata(e2))[0, 1], t))
            res.sort()
            return res
        cand_add = [t for t in all_t if t not in B]
        if len(cand_add) > 150:
            cand_add = list(rng.choice(cand_add, 150, replace=False))
        allcols = all_t
        for fname, cols, ops, op in [("basis B12", np.array(B), B, "remove"), ("basis B12", np.array(B), cand_add, "add"),
                                     ("all tests", allcols, list(rng.choice(allcols, min(150, N), replace=False)) if N > 150 else list(allcols), "remove")]:
            res = stab(cols, ops, op)
            rhos = np.array([r for r, _ in res])
            P(f"| {fname} | {op} one test | {len(res)} | {rhos.min():.4f} | {np.median(rhos):.4f} | {lab[res[0][1]]} |")
        # basis vs all
        P(f"\nSpearman(E_basis, E_all) = {spearmanr(Es['basis B12'][iu], Es['all tests'][iu])[0]:.3f}; "
          f"Spearman(E_all, E_all chi-bal) = {spearmanr(Es['all tests'][iu], Es['all, chi-balanced'][iu])[0]:.3f}")
    (pathlib.Path(__file__).parent / "Q_testfamily_out.md").write_text("\n".join(out_lines) + "\n")


if __name__ == "__main__":
    main()
