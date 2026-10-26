import sys
sys.setrecursionlimit(10000)
def gp(n, k):
    E = set()
    for i in range(n):
        E |= {(i, (i+1) % n), (i, n+i), (n+i, n+(i+k) % n)}
    adj = [set() for _ in range(2*n)]
    for u, v in E:
        adj[u].add(v); adj[v].add(u)
    return adj
def odd_girth(adj):
    from collections import deque
    best = 99; N = len(adj)
    for s in range(N):
        d = {(s, 0): 0}; q = deque([(s, 0)])
        while q:
            u, p = q.popleft()
            for v in adj[u]:
                if (v, 1-p) not in d: d[(v, 1-p)] = d[(u, p)] + 1; q.append((v, 1-p))
        best = min(best, d.get((s, 1), 99))
    return best
def hom_to_cycle(adj, c):
    N = len(adj); order = []; seen = set()
    # BFS order for strong propagation
    from collections import deque
    q = deque([0]); seen.add(0)
    while q:
        u = q.popleft(); order.append(u)
        for v in sorted(adj[u]):
            if v not in seen: seen.add(v); q.append(v)
    col = [-1]*N
    def ok(u, x):
        return all(col[v] < 0 or (col[v]-x) % c in (1, c-1) for v in adj[u])
    def rec(i):
        if i == N: return True
        u = order[i]
        for x in (range(c) if i else [0]):
            if ok(u, x):
                col[u] = x
                if rec(i+1): return True
                col[u] = -1
        return False
    return rec(0)
for n in range(3, 13):
    for k in range(1, (n-1)//2 + 1):
        adj = gp(n, k); g = odd_girth(adj)
        if g in (3, 99): continue
        print(f"GP({n},{k}) odd girth {g}: maps to C{g}? {hom_to_cycle(adj, g)}")
