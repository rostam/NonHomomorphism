"""Euclidean alpha-profile metric on homomorphism classes of graphs.

phi(G)_T = alpha(T, G) / e(T) over a fixed family of test graphs T (G is the
*target*), scaled by chi-balanced weights w_T = 1/sqrt(#tests with chi(T)), and
E(G, H) = ||phi(G) - phi(H)||_2.  phi is constant on hom-equivalence classes,
and reverses the homomorphism order (G -> H  =>  phi(G) >= phi(H)).

Test family: the 85 cores of data/alpha.csv (all cores on <= 8 vertices plus
C9, C11, Petersen, Grotzsch, Icosahedron).  Plotted graphs: those 85 cores,
optionally the 1276 cores on <= 9 vertices, and the generalized Petersen
graphs GP(n,k), 3 <= n <= 12 (data/gp_profiles.csv, from code/gp_profiles).

Usage:  python alpha_profile.py
Writes  figures/alpha_profile_pca.png  and  html/alpha_profile_3d.html
"""
import csv
import json
import pathlib
from collections import defaultdict

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = pathlib.Path(__file__).resolve().parent.parent
DATA, FIG, HTML = ROOT / "data", ROOT / "figures", ROOT / "html"

# categorical slots in chi order (validated light / dark palettes)
SLOTS = ["#2a78d6", "#eb6834", "#1baf7a", "#eda100", "#e87ba4", "#008300", "#6250d6", "#e34948"]
SLOTS_DARK = ["#3987e5", "#d95926", "#199e70", "#c98500", "#d55181", "#008300", "#9085e9", "#e66767"]
CHI_MIN = 2
NAMED = {"Petersen", "Grotzsch", "Icosahedron", "W5", "W7"}


def load(suffix):
    rows = list(csv.reader(open(DATA / f"alpha{suffix}.csv")))
    lab = rows[0][1:]
    a = np.array([[float(x) for x in r[1:]] for r in rows[1:]])  # a[i, j] = alpha(lab[i], lab[j])
    meta = {r["label"]: r for r in csv.DictReader(open(DATA / f"cores_meta{suffix}.csv"))}
    info = {k: np.array([int(meta[l][k]) for l in lab]) for k in ("n", "m", "chi")}
    assert a[lab.index("K2"), lab.index("K3")] == 0 and a[lab.index("K3"), lab.index("K2")] == 1
    return lab, a, info


def is_clique(l):
    return l[0] == "K" and l[1:].isdigit()


def is_named(l):
    return is_clique(l) or (l[0] in "CW" and l[1:].isdigit()) or l in NAMED


def gp_label(name):
    return name.replace(";", ",")


def main():
    lab, a, info = load("")
    tests = lab                                   # the 85 cores are the test family
    t_chi = info["chi"]
    t_m = info["m"]
    cnt = defaultdict(int)
    for c in t_chi:
        cnt[c] += 1
    w = np.array([1 / np.sqrt(cnt[c]) for c in t_chi])

    def profile(alpha_cols):                     # alpha_cols[t, g] = alpha(test t, graph g)
        return (alpha_cols / t_m[:, None]).T * w

    X = profile(a)
    mu = X.mean(0)
    U, S, Vt = np.linalg.svd(X - mu, full_matrices=False)
    var = S ** 2 / (S ** 2).sum()
    proj = lambda Z: (Z - mu) @ Vt[:3].T
    Y = proj(X)

    # generalized Petersen graphs
    gp = list(csv.DictReader(open(DATA / "gp_profiles.csv")))
    assert all(r["exact_all"] == "true" for r in gp), "some GP profile entries are only upper bounds"
    G_alpha = np.array([[float(r[t]) for t in tests] for r in gp]).T
    GY = proj(profile(G_alpha))
    gp_names = [gp_label(r["target"]) for r in gp]
    gp_equiv = [r["equiv"] for r in gp]
    gp_core = []                                 # nearest core (distance 0 means hom-equivalent on these tests)
    for k in range(len(gp)):
        d = np.linalg.norm(X - profile(G_alpha)[k], axis=1)
        j = int(d.argmin())
        gp_core.append((lab[j], float(d[j])))

    # circular cliques K_{p/q}
    cc = sorted(csv.DictReader(open(DATA / "circular_profiles.csv")), key=lambda r: int(r["p"]) / int(r["q"]))
    assert all(r["exact_all"] == "true" for r in cc), "some circular-clique entries are only upper bounds"
    C_alpha = np.array([[float(r[t]) for t in tests] for r in cc]).T
    CX = profile(C_alpha)
    CY = proj(CX)
    cc_pq = [(int(r["p"]), int(r["q"])) for r in cc]
    cc_chi = [-(-p // q) for p, q in cc_pq]
    cc_core = []
    for k in range(len(cc)):
        d = np.linalg.norm(X - CX[k], axis=1)
        j = int(d.argmin())
        cc_core.append(lab[j] if d[j] < 1e-9 else "-")
    for (pp, qq), nm in [((5, 2), "C5"), ((7, 3), "C7"), ((9, 4), "C9"), ((11, 5), "C11"), ((8, 1), "K8"), ((3, 1), "K3")]:
        assert cc_core[cc_pq.index((pp, qq))] == nm, f"K{pp}/{qq} should coincide with {nm}"
    cc_name = [f"K{p}" if q == 1 else f"K{p}/{q}" for p, q in cc_pq]
    print("circular cliques (p/q, PC1, PC2, same point as):")
    for nm, (pp, qq), y, c in zip(cc_name, cc_pq, CY, cc_core):
        print(f"   {nm:7s} {pp/qq:5.2f}  {y[0]:+.4f} {y[1]:+.4f}  {c}")

    N = len(lab)
    E = np.sqrt(((X[:, None] - X[None]) ** 2).sum(-1))
    J = np.eye(N) - 1 / N
    print(f"85 cores, chi-balanced weights: min Gram eigenvalue {np.linalg.eigvalsh(-0.5 * J @ E**2 @ J).min():.1e}")
    print(f"variance PC1/PC2/PC3: {var[0]:.1%} / {var[1]:.1%} / {var[2]:.1%}")
    print("generalized Petersen graphs -> nearest core (E distance):")
    for nm, eq, (c, d) in zip(gp_names, gp_equiv, gp_core):
        print(f"   {nm:10s} equiv={eq:4s} nearest core {c:12s} E={d:.4f}")

    # group GP graphs / circular cliques that land on the same point
    def group(P2, names, keep=lambda k: True):
        g = defaultdict(list)
        for k, nm in enumerate(names):
            if keep(k):
                g[tuple(np.round(P2[k, :2], 6))].append(nm)
        return g
    groups = group(GY, gp_names)
    # circular cliques: skip the q = 1 ones (they are the complete graphs, drawn already)
    cgroups = group(CY, cc_name, keep=lambda k: cc_pq[k][1] > 1)
    stair = []                                   # distinct landing points in p/q order
    for k in range(len(cc)):
        pt = tuple(np.round(CY[k, :3], 6))
        if not stair or stair[-1] != pt:
            stair.append(pt)
    stair = np.array(stair)

    # ---- static figure --------------------------------------------------------
    chis = sorted(set(info["chi"]))
    col = {c: SLOTS[c - CHI_MIN] for c in chis}
    cl_idx = sorted([i for i, l in enumerate(lab) if is_clique(l)], key=lambda i: int(lab[i][1:]))
    cc_nc = [k for k in range(len(cc)) if cc_pq[k][1] > 1]

    def draw(ax, p, q, zoom=None, skip_labels=(), label_side=False):
        for c in chis:
            s_ = (info["chi"] == c) & np.array([not is_clique(l) for l in lab])
            ax.scatter(Y[s_, p], Y[s_, q], s=26, c=col[c], edgecolor="white", linewidth=0.8, alpha=0.6, zorder=2)
        ax.plot(Y[cl_idx, p], Y[cl_idx, q], color="#444", lw=1.2, ls="-", zorder=3)
        ax.plot(stair[:, p], stair[:, q], color="#7a3fb0", lw=1.6, ls=(0, (4, 2)), zorder=3.5)
        for k in cc_nc:
            ax.scatter(CY[k, p], CY[k, q], s=95, marker="s", c=col[min(cc_chi[k], max(chis))],
                       edgecolor="#4b1f73", linewidth=1.6, zorder=4.5)
        for i in cl_idx:
            ax.scatter(Y[i, p], Y[i, q], s=190, c=col[info["chi"][i]], edgecolor="black", linewidth=1.6, zorder=5)
            ax.annotate(lab[i], (Y[i, p], Y[i, q]), fontsize=12, fontweight="bold", xytext=(8, 6),
                        textcoords="offset points", zorder=6)
        for k in range(len(gp)):
            ax.scatter(GY[k, p], GY[k, q], s=150, marker="D", facecolor="none", edgecolor="black",
                       linewidth=1.6, zorder=7)
        for i, l in enumerate(lab):
            if is_named(l) and not is_clique(l) and l not in skip_labels:
                ax.annotate(l, (Y[i, p], Y[i, q]), fontsize=9, color="#333", xytext=(-10, 0) if label_side else (6, -11),
                            ha="right" if label_side else "left", textcoords="offset points", zorder=6)
        if zoom is not None:
            ax.set_xlim(*zoom[0]); ax.set_ylim(*zoom[1])
        ax.set_xlabel(f"PC{p+1} ({var[p]:.0%} of variance)")
        ax.set_ylabel(f"PC{q+1} ({var[q]:.0%} of variance)")
        ax.grid(color="#e6e6e3", lw=0.6, zorder=0); ax.set_axisbelow(True)
        for sp in ("top", "right"):
            ax.spines[sp].set_visible(False)

    box = dict(boxstyle="round,pad=0.3", fc="white", ec="#888", lw=0.7)
    cbox = dict(boxstyle="round,pad=0.3", fc="#f4ecfb", ec="#7a3fb0", lw=0.8)
    fig, ax = plt.subplots(1, 2, figsize=(20, 8.8), gridspec_kw={"width_ratios": [1.05, 1]})
    draw(ax[0], 0, 1, skip_labels={"C7", "C9", "C11"})
    ax[0].set_title("(a) complete graphs (circles), circular cliques K_p/q (squares, dashed staircase), GP(n,k) (diamonds)",
                    loc="left", fontsize=11.5)
    tf = Y[:, 0] > 0.5 * Y[:, 0].max()
    zx0, zx1 = Y[tf, 0].min(), Y[tf, 0].max()
    zy0, zy1 = Y[tf, 1].min(), Y[tf, 1].max()
    dx, dy = zx1 - zx0, zy1 - zy0
    zx, zy = (zx0 - 1.5 * dx, zx1 + 1.6 * dx), (zy0 - 0.08 * dy, zy1 + 0.08 * dy)
    inzoom = lambda x, y: zx[0] <= x <= zx[1] and zy[0] <= y <= zy[1]
    ax[0].add_patch(plt.Rectangle((zx0 - 0.15 * dx, zy[0]), 1.3 * dx, zy[1] - zy[0], fill=False, ls="--", lw=1, color="#666"))
    draw(ax[1], 0, 1, zoom=(zx, zy), label_side=True)
    ax[1].set_title("(b) zoom on the dashed box (triangle-free end)", loc="left", fontsize=11.5)

    def column(ax_, items, xtext, bbox, ha):
        items = sorted(items, reverse=True)
        ys = np.linspace(zy[1] - 0.06 * (zy[1] - zy[0]), zy[0] + 0.06 * (zy[1] - zy[0]), max(len(items), 2))
        for (y, x, names), ty in zip(items, ys):
            ax_.annotate("\n".join(", ".join(names[i:i + 4]) for i in range(0, len(names), 4)), (x, y),
                         xytext=(xtext, ty), textcoords="data", fontsize=9, va="center", ha=ha, bbox=bbox, zorder=8,
                         arrowprops=dict(arrowstyle="-", color="#777", lw=0.8))

    gin = [(k[1], k[0], v) for k, v in groups.items() if inzoom(*k)]
    gout = [(k[1], k[0], v) for k, v in groups.items() if not inzoom(*k)]
    cin = [(k[1], k[0], v) for k, v in cgroups.items() if inzoom(*k)]
    cout = [(k[1], k[0], v) for k, v in cgroups.items() if not inzoom(*k)]
    column(ax[1], gin, zx1 + 0.35 * dx, box, "left")
    column(ax[1], cin, zx0 - 0.45 * dx, cbox, "right")
    for y, x, names in gout:
        ax[0].annotate(", ".join(names), (x, y), xytext=(45, 48), textcoords="offset points", fontsize=9,
                       bbox=box, zorder=8, arrowprops=dict(arrowstyle="-", color="#777", lw=0.8))
    for y, x, names in cout:
        off = (-95, 2) if y > 0.015 else (14, -26)          # the group above K3 goes to the left
        ax[0].annotate(", ".join(names), (x, y), xytext=off, textcoords="offset points", fontsize=9,
                       ha="right" if off[0] < 0 else "left", bbox=cbox, zorder=8, arrowprops=dict(arrowstyle="-", color="#7a3fb0", lw=0.8))
    handles = [plt.Line2D([], [], marker="o", ls="", markersize=8, markerfacecolor=col[c], markeredgecolor="white",
                          label=f"χ = {c}") for c in chis]
    handles += [plt.Line2D([], [], marker="o", ls="-", color="#444", markersize=12, markerfacecolor="#ccc",
                           markeredgecolor="black", markeredgewidth=1.6, label="complete graph Kₙ"),
                plt.Line2D([], [], marker="s", ls=(0, (4, 2)), color="#7a3fb0", markersize=9, markerfacecolor="#ccc",
                           markeredgecolor="#4b1f73", markeredgewidth=1.6, label="circular clique K_p/q (p ≤ 13)"),
                plt.Line2D([], [], marker="D", ls="", markersize=9, markerfacecolor="none", markeredgecolor="black",
                           markeredgewidth=1.6, label="generalized Petersen GP(n,k)")]
    ax[0].legend(handles=handles, frameon=True, framealpha=0.95, edgecolor="#ddd", fontsize=9.5, loc="lower center", ncol=2)
    fig.suptitle("The Euclidean α-profile space (85 test cores, χ-balanced weights)", x=0.01, ha="left", fontsize=15)
    fig.tight_layout()
    FIG.mkdir(exist_ok=True)
    fig.savefig(FIG / "alpha_profile_pca.png", dpi=140)
    print("wrote", FIG / "alpha_profile_pca.png")

    # ---- interactive 3D -------------------------------------------------------
    lab9, a9, info9 = load("_n9")
    idx = [lab9.index(t) for t in tests]
    Y9 = proj(profile(a9[idx, :]))
    payload = {"var": [round(float(v), 4) for v in var[:3]], "sets": {}}
    raw = lambda A: np.round((A / t_m[:, None]).T, 5).tolist()     # full profiles, for the distance tool
    payload.update({"tests": lab, "w": np.round(w, 6).tolist(), "tm": t_m.tolist()})
    for key, (L, Yk, inf, Pk) in {"n8": (lab, Y, info, raw(a)), "n9": (lab9, Y9, info9, raw(a9[idx, :]))}.items():
        payload["sets"][key] = {
            "x": Yk[:, 0].round(5).tolist(), "y": Yk[:, 1].round(5).tolist(), "z": Yk[:, 2].round(5).tolist(),
            "label": L, "chi": inf["chi"].tolist(), "n": inf["n"].tolist(), "m": inf["m"].tolist(),
            "clique": [is_clique(l) for l in L], "named": [is_named(l) for l in L], "P": Pk}
    payload["gp"] = {"x": GY[:, 0].round(5).tolist(), "y": GY[:, 1].round(5).tolist(), "z": GY[:, 2].round(5).tolist(),
                     "label": gp_names, "n": [int(r["n"]) for r in gp], "m": [int(r["m"]) for r in gp],
                     "equiv": [c if d < 1e-9 else "-" for c, d in gp_core], "P": raw(G_alpha)}
    payload["circ"] = {"x": CY[:, 0].round(5).tolist(), "y": CY[:, 1].round(5).tolist(), "z": CY[:, 2].round(5).tolist(),
                       "label": cc_name, "pq": [p_ / q_ for p_, q_ in cc_pq], "q": [q_ for _, q_ in cc_pq],
                       "chi": cc_chi, "at": cc_core, "P": raw(C_alpha)}
    tpl = (pathlib.Path(__file__).parent / "alpha_profile_3d.tpl").read_text()
    html = (tpl.replace("{{DATA}}", json.dumps(payload))
               .replace("{{SLOTS}}", json.dumps(SLOTS)).replace("{{SLOTS_DARK}}", json.dumps(SLOTS_DARK)))
    HTML.mkdir(exist_ok=True)
    (HTML / "alpha_profile_3d.html").write_text(html)
    print("wrote", HTML / "alpha_profile_3d.html")


if __name__ == "__main__":
    main()
