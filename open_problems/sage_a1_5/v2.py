import sys; sys.path.insert(0, sys.argv[1])
import networkx as nx, json, subprocess
from graphs import BIN, g6
def solve(G, H, t=120):
    r = json.loads(subprocess.run([BIN, g6(nx.convert_node_labels_to_integers(G)), g6(nx.convert_node_labels_to_integers(H)), str(t)], capture_output=True, text=True).stdout)
    return r["value"] if r["exact"] else f"<={r['value']}?"
cubic = {"K4": nx.complete_graph(4), "prism": nx.circular_ladder_graph(3), "K3,3": nx.complete_bipartite_graph(3, 3),
         "cube": nx.hypercube_graph(3), "Petersen": nx.petersen_graph(), "Heawood": nx.heawood_graph(),
         "Mobius-Kantor": nx.moebius_kantor_graph(), "dodecahedron": nx.dodecahedral_graph(), "Desargues": nx.desargues_graph()}
for s in range(1, 6): cubic[f"rand cubic n=16 s{s}"] = nx.random_regular_graph(3, 16, seed=s)
C5, C7, K2, K3 = nx.cycle_graph(5), nx.cycle_graph(7), nx.complete_graph(2), nx.complete_graph(3)
print("G | n | |L(G),K2| | |L(G),C5| | |L(G),C7| | |L(G),K3|")
for name, G in cubic.items():
    L = nx.line_graph(G)
    print(name, G.number_of_nodes(), solve(L, K2), solve(L, C5), solve(L, C7), solve(L, K3), flush=True)
