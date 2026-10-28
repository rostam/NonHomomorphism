import sys; sys.path.insert(0, sys.argv[1])
import networkx as nx, json, subprocess, math
from graphs import BIN, g6, gen_petersen
def solve(G, H, t=60):
    r = json.loads(subprocess.run([BIN, g6(nx.convert_node_labels_to_integers(G)), g6(nx.convert_node_labels_to_integers(H)), str(t)], capture_output=True, text=True).stdout)
    return r["value"] if r["exact"] else f"<={r['value']}?"
K2 = nx.complete_graph(2)
def reps(n, k):
    s = {k % n, (-k) % n}
    if math.gcd(n, k) == 1:
        inv = pow(k, -1, n); s |= {inv, n - inv}
    return sorted(min(x, n - x) for x in s)
for n in range(19, 32, 2):
    for k in range(2, (n - 1) // 2 + 1):
        print(n, k, reps(n, k), solve(gen_petersen(n, k), K2), flush=True)
