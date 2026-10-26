import csv,numpy as np
from P_g6 import g6
D='/home/rostam/kara/NonHomomorphism/open_problems/metric_space/data/'
rows=list(csv.reader(open(D+'alpha_n9.csv'))); lab=rows[0][1:]; N=len(lab)
A=np.array([[int(x) for x in r[1:]] for r in rows[1:]])   # A[s,t]=alpha(s,t)
meta={r['label']:r for r in csv.DictReader(open(D+'cores_meta_n9.csv'))}
Gr=[g6(meta[l]['graph6']) for l in lab]; chi=[int(meta[l]['chi']) for l in lab]
def hom(n,E,m,F):
    adj=[[] for _ in range(n)]
    for a,b in E: adj[a].append(b); adj[b].append(a)
    Fs=set(F)|{(b,a) for a,b in F}; f=[-1]*n
    order=sorted(range(n),key=lambda v:-len(adj[v]))
    def rec(i):
        if i==n: return True
        v=order[i]
        for c in range(m):
            if all(f[u]<0 or (c,f[u]) in Fs for u in adj[v]):
                f[v]=c
                if rec(i+1): return True
        f[v]=-1
        return False
    return rec(0)
stats={}; ex=[]
for g in range(N):
    for h in range(g+1,N):
        d=A[:,g]!=A[:,h]
        if d.sum()!=1: continue
        t=int(np.flatnonzero(d)[0])
        G,H=(g,h) if t==g else (h,g)     # separated only by test G
        hg=A[H,G]==0; agh=A[G,H]
        between=[s for s in range(N) if s not in (G,H) and A[H,s]==0 and A[s,G]==0 and A[s,H]>0]
        n,E=Gr[G]; m,F=Gr[H]
        crit=(hom(n,[x for x in E if x!=e],m,F) for e in E)
        key=(bool(hg),int(agh),crit,len(between)==0,(chi[H],chi[G]))
        stats[key]=stats.get(key,0)+1
for k,v in sorted(stats.items(),key=lambda x:-x[1]): print('H->G',k[0],'alpha(G,H)',k[1],'G H-critical',k[2],'cover',k[3],'(chiH,chiG)',k[4],':',v)
Hs={}
for g in range(N):
    for h in range(g+1,N):
        d=A[:,g]!=A[:,h]
        if d.sum()!=1: continue
        t=int(np.flatnonzero(d)[0]); H=h if t==g else g
        Hs[lab[H]]=Hs.get(lab[H],0)+1
print('distinct lower members H:',len(Hs), sorted(Hs.items(),key=lambda x:-x[1])[:8])
