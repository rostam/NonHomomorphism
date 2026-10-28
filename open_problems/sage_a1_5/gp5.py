import sys; sys.path.insert(0, sys.argv[1])
import networkx as nx, json, subprocess
from graphs import BIN, g6, gen_petersen
def solve(G, H, t=120):
    r = json.loads(subprocess.run([BIN, g6(nx.convert_node_labels_to_integers(G)), g6(nx.convert_node_labels_to_integers(H)), str(t)], capture_output=True, text=True).stdout)
    return r["value"] if r["exact"] else -r["value"]
C5 = nx.cycle_graph(5)
for n in range(23, 35):
    for k in (2, 3, 4):
        print(n, k, solve(gen_petersen(n, k), C5), flush=True)
