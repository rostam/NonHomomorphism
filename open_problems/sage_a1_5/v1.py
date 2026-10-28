import sys; sys.path.insert(0, sys.argv[1])
from graphs import nonhom
def v(g, h): r = nonhom(g, h, 60); return r["value"] if r["exact"] else f">={r['value']}?"
print("C_n^2: n | K3 | n mod 3 | C5 | C7 | C9 | C11 | K2 | ceil(n/2)")
for n in range(6, 26):
    g = f"power_cycle {n} 2"
    print(n, v(g, "K3"), n % 3, v(g, "C5"), v(g, "C7"), v(g, "C9"), v(g, "C11"), v(g, "K2"), -(-n // 2))
print("Wheels (rim m): m | C5 | K2 | ceil(m/2)")
for m in range(3, 21):
    g = f"wheel {m+1}"; print(m, v(g, "C5"), v(g, "K2"), -(-m // 2))
