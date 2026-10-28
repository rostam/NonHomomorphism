import sys; sys.path.insert(0, sys.argv[1])
import networkx as nx, json, subprocess
from graphs import BIN, g6
def solve(G, H, t=900):
    r = json.loads(subprocess.run([BIN, g6(G), g6(H), str(t)], capture_output=True, text=True).stdout)
    return r["value"] if r["exact"] else f"<={r['value']}?"
for n, k in [(21, 7), (21, 9), (22, 9), (22, 11), (23, 5), (23, 7), (24, 5), (25, 5), (25, 11)]:
    print(n, f"C{k}", solve(nx.circulant_graph(n, [1, 2]), nx.cycle_graph(k)), flush=True)
