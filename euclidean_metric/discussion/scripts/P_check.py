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
D='/home/rostam/kara/NonHomomorphism/open_problems/metric_space/data/'
for suf in ['','_n9']:
    rows=list(csv.reader(open(D+f'alpha{suf}.csv'))); lab=rows[0][1:]
    A={r[0]:{lab[j]:int(x) for j,x in enumerate(r[1:])} for r in rows[1:]}
    meta={r['label']:r for r in csv.DictReader(open(D+f'cores_meta{suf}.csv'))}
    m={l:int(meta[l]['m']) for l in lab}
    om={l:omega(*g6(meta[l]['graph6'])) for l in lab}
    bad=0
    for g in lab:
        for h in lab:
            dom=all(A[t][g]>=A[t][h] for t in lab)
            if dom!=(A[g][h]==0): bad+=1
    # Motzkin-Straus bound phi_T(G)<=1/omega(G); clique formula
    def tur(k,r):
        r=min(r,k); q,s=divmod(k,r); return (k*k-(s*(q+1)**2+(r-s)*q*q))//2
    mb=sum(1 for t in lab for g in lab if A[t][g]/m[t]>1/om[g]+1e-12)
    kb=sum(1 for t in lab if t.startswith('K') and t[1:].isdigit() for g in lab if A[t][g]!=int(t[1:])*(int(t[1:])-1)//2-tur(int(t[1:]),om[g]))
    print(suf or 'n<=8',len(lab),'order-embedding failures',bad,'MS-bound failures',mb,'clique-formula failures',kb)
