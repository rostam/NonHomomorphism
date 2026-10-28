import sys; sys.path.insert(0, sys.argv[1])
import networkx as nx, json, subprocess
from graphs import BIN, g6, gen_petersen
def solve(G, H, t=120):
    r = json.loads(subprocess.run([BIN, g6(nx.convert_node_labels_to_integers(G)), g6(nx.convert_node_labels_to_integers(H)), str(t)], capture_output=True, text=True).stdout)
    return r["value"] if r["exact"] else f"<={r['value']}?"
K2, C5 = nx.complete_graph(2), nx.cycle_graph(5)
for n in range(int(sys.argv[2]), int(sys.argv[3]) + 1):
    for k in range(1, (n - 1) // 2 + 1):
        G = gen_petersen(n, k)
        print(n, k, solve(G, K2), solve(G, C5), flush=True)
