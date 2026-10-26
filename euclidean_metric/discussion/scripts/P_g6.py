import csv,itertools
def g6(x):
    d=[ord(c)-63 for c in x]; n=d[0]; bits=[(v>>(5-i))&1 for v in d[1:] for i in range(6)]
    E=set();k=0
    for j in range(1,n):
        for i in range(j):
            if bits[k]: E.add((i,j))
            k+=1
    return n,E
def omega(n,E):
    best=1
    for r in range(2,n+1):
        if any(all((a,b) in E for a,b in itertools.combinations(S,2)) for S in itertools.combinations(range(n),r)): best=r
        else: break
    return best
