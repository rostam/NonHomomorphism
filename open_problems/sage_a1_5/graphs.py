"""Parse a restricted graph-spec language (no eval) and call the |G,H| solver."""
import itertools, json, os, subprocess, networkx as nx
BIN = os.environ.get("NHCLI", os.path.join(os.path.dirname(os.path.abspath(__file__)), "nhcli/target/release/nhcli"))

def kneser(n, k):
    vs = list(itertools.combinations(range(n), k))
    G = nx.Graph(); G.add_nodes_from(vs)
    G.add_edges_from((a, b) for a, b in itertools.combinations(vs, 2) if not set(a) & set(b))
    return G

def mycielski(k):  # M(2)=K2, M(3)=C5, M(4)=Grotzsch
    return nx.mycielski_graph(k)

def gen_petersen(n, k):
    G = nx.Graph()
    for i in range(n):
        G.add_edge(i, (i + 1) % n); G.add_edge(i, n + i); G.add_edge(n + i, n + (i + k) % n)
    return G

def power_cycle(n, k):  # C_n^k
    return nx.circulant_graph(n, list(range(1, k + 1)))

FAMILIES = {
    "complete": (1, lambda a: nx.complete_graph(a[0])),
    "cycle": (1, lambda a: nx.cycle_graph(a[0])),
    "path": (1, lambda a: nx.path_graph(a[0])),
    "wheel": (1, lambda a: nx.wheel_graph(a[0])),  # wheel n = hub + C_{n-1}
    "hypercube": (1, lambda a: nx.hypercube_graph(a[0])),
    "mycielski": (1, lambda a: mycielski(a[0])),
    "complete_bipartite": (2, lambda a: nx.complete_bipartite_graph(*a)),
    "complete_multipartite": (None, lambda a: nx.complete_multipartite_graph(*a)),
    "kneser": (2, lambda a: kneser(*a)),
    "gen_petersen": (2, lambda a: gen_petersen(*a)),
    "power_cycle": (2, lambda a: power_cycle(*a)),
    "circulant": (None, lambda a: nx.circulant_graph(a[0], a[1:])),
    "grid": (2, lambda a: nx.grid_2d_graph(*a)),
    "torus_grid": (2, lambda a: nx.grid_2d_graph(*a, periodic=True)),
    "random_regular": (3, lambda a: nx.random_regular_graph(a[0], a[1], seed=a[2])),
    "gnp": (3, lambda a: nx.gnp_random_graph(a[0], a[1] / 100, seed=a[2])),  # p given in percent
}
NAMED = {"petersen": nx.petersen_graph, "dodecahedron": nx.dodecahedral_graph, "icosahedron": nx.icosahedral_graph,
         "octahedron": nx.octahedral_graph, "heawood": nx.heawood_graph, "pappus": nx.pappus_graph,
         "desargues": nx.desargues_graph, "chvatal": nx.chvatal_graph, "clebsch": lambda: nx.circulant_graph(16, [1,2]),
         "mobius_kantor": nx.moebius_kantor_graph, "tutte": nx.tutte_graph, "frucht": nx.frucht_graph,
         "mcgee": lambda: nx.LCF_graph(24, [12, 7, -7], 8), "grotzsch": lambda: mycielski(4)}

def parse(spec):
    """Specs: 'petersen' | 'cycle 7' | 'kneser 6 2' | 'circulant 13 1 5' | 'edges 0-1 1-2 2-0' | 'line <spec>' | 'complement <spec>'."""
    import re
    m = re.fullmatch(r"\s*([KCPWQ])_?\{?(\d+)\}?(?:\s*,\s*(\d+))?\s*", spec)
    if m:
        L, a, b = m.group(1), int(m.group(2)), m.group(3)
        if L == "K" and b: spec = f"complete_bipartite {a} {b}"
        else: spec = {"K": "complete", "C": "cycle", "P": "path", "W": "wheel", "Q": "hypercube"}[L] + f" {a}"
    t = spec.strip().split()
    if not t: raise ValueError("empty spec")
    head, rest = t[0].lower(), t[1:]
    if head in ("line", "complement", "mycielskian"):
        inner = parse(" ".join(rest))
        G = {"line": nx.line_graph, "complement": nx.complement, "mycielskian": nx.mycielskian}[head](inner)
        return nx.convert_node_labels_to_integers(G)
    if head == "edges":
        G = nx.Graph()
        for e in rest:
            u, v = e.split("-"); G.add_edge(int(u), int(v))
        return nx.convert_node_labels_to_integers(G)
    if head in NAMED and not rest: return nx.convert_node_labels_to_integers(NAMED[head]())
    if head in FAMILIES:
        arity, f = FAMILIES[head]; a = [int(x) for x in rest]
        if arity is not None and len(a) != arity: raise ValueError(f"{head} takes {arity} integer args")
        G = f(a)
        if G.number_of_nodes() > 64: raise ValueError("graphs limited to 64 vertices")
        return nx.convert_node_labels_to_integers(G)
    raise ValueError(f"unknown graph spec '{spec}' (use concrete integers, e.g. 'power_cycle 11 2', 'K5', 'C7', 'K3,3'; see tool description)")

def g6(G): return nx.to_graph6_bytes(G, header=False).decode().strip()

def nonhom(gspec, hspec, timeout=60):
    G, H = parse(gspec), parse(hspec)
    info = {"G": gspec, "H": hspec, "nG": G.number_of_nodes(), "mG": G.number_of_edges(),
            "nH": H.number_of_nodes(), "mH": H.number_of_edges()}
    if info["mG"] == 0: return {**info, "value": 0, "exact": True}
    timeout = max(1, min(int(timeout), 120))
    r = json.loads(subprocess.run([BIN, g6(G), g6(H), str(timeout)], capture_output=True, text=True, timeout=timeout + 30).stdout)
    r.pop("mapping", None)
    return {**info, **r}
