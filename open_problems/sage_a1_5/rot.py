import re, sys
vals = {}
for line in open("data/gp2.txt"):
    p = line.split()
    if len(p) == 4 and p[0].isdigit() and p[2].isdigit(): vals[(int(p[0]), int(p[1]))] = int(p[2])
for line in open("data/gp3.txt"):
    m = re.match(r"(\d+) (\d+) \[.*\] (\d+)$", line.strip())
    if m: vals[(int(m[1]), int(m[2]))] = int(m[3])
for t in "5 1 2;5 2 3;6 2 4;7 1 2;7 2 4;7 3 4;8 2 4;9 1 2;9 2 5;9 3 4;9 4 5;10 2 6;10 4 4;11 1 2;11 2 6;11 3 4;11 4 4;11 5 6;12 2 6;12 4 6;13 1 2;13 2 7;13 3 4;13 4 4".split(";"):
    a, b, c = map(int, t.split()); vals[(a, b)] = c
def rot(n, k):
    N = 2 * n; best = 10**9
    for t in range(1, N):
        for b in range(N):
            cu = [((t * i) % N) * 2 // N for i in range(n)]
            cv = [((t * i + b) % N) * 2 // N for i in range(n)]
            cost = sum(cu[i] == cu[(i + 1) % n] for i in range(n)) + sum(cu[i] == cv[i] for i in range(n)) + sum(cv[i] == cv[(i + k) % n] for i in range(n))
            best = min(best, cost)
    return best
ok = 0
for (n, k), v in sorted(vals.items()):
    r = rot(n, k)
    if r == v: ok += 1
    else: print("n=%d k=%d exact=%d rotation=%d" % (n, k, v, r))
print("match", ok, "of", len(vals))
