import sys; sys.path.insert(0, sys.argv[1])
import networkx as nx, json, subprocess
from graphs import BIN, g6
def solve(G, H, t=300):
    r = json.loads(subprocess.run([BIN, g6(nx.convert_node_labels_to_integers(G)), g6(nx.convert_node_labels_to_integers(H)), str(t)], capture_output=True, text=True).stdout)
    return r["value"] if r["exact"] else f"<={r['value']}?"
C5, K2 = nx.cycle_graph(5), nx.complete_graph(2)
print("d-regular G | d | n | predicted n*floor((d-1)^2/4) | |L(G),K2| | |L(G),C5|")
for name, G, d in [("K5", nx.complete_graph(5), 4), ("K6", nx.complete_graph(6), 5), ("K4,4", nx.complete_bipartite_graph(4, 4), 4),
                   ("K5,5", nx.complete_bipartite_graph(5, 5), 5), ("C8^2 (4-reg)", nx.circulant_graph(8, [1, 2]), 4),
                   ("C9^2 (4-reg)", nx.circulant_graph(9, [1, 2]), 4)]:
    n = G.number_of_nodes(); L = nx.line_graph(G)
    print(name, d, n, n * ((d - 1) ** 2 // 4), solve(L, K2), solve(L, C5), flush=True)
