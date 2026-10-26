import csv, numpy as np, pathlib, itertools
from math import comb
from scipy.stats import spearmanr, rankdata
R=pathlib.Path("/home/rostam/kara/NonHomomorphism/open_problems/metric_space/data")
D=pathlib.Path(__file__).parent.parent/"discussion"
def mat(p):
    r=list(csv.reader(open(p))); return r[0][1:], np.array([[float(x) for x in q[1:]] for q in r[1:]])
lab,a=mat(R/"alpha_n9.csv"); N=len(lab); ix={l:i for i,l in enumerate(lab)}
meta={q["label"]:q for q in csv.DictReader(open(R/"cores_meta_n9.csv"))}
n=np.array([int(meta[l]["n"]) for l in lab]); m=np.array([int(meta[l]["m"]) for l in lab]); chi=np.array([int(meta[l]["chi"]) for l in lab])
def g6(s):
    s=s.strip().encode(); k=s[0]-63; bits=[]
    for c in s[1:]: bits+= [(c-63)>>(5-i)&1 for i in range(6)]
    A=np.zeros((k,k),bool); b=0
    for v in range(1,k):
        for u in range(v):
            if bits[b]: A[u,v]=A[v,u]=True
            b+=1
    return A
adj=[g6(meta[l]["graph6"]) for l in lab]
def omega(A):
    k=len(A); best=1
    def ext(C,cand):
        nonlocal best; best=max(best,len(C))
        for v in list(cand):
            ext(C+[v],[w for w in cand if w>v and A[v,w]])
    ext([],list(range(k))); return best
def oddgirth(A):
    k=len(A); best=10**9
    for s in range(k):
        dist={(s,0):0}; q=[(s,0)]
        for x in q:
            for v in np.where(A[x[0]])[0]:
                y=(v,1-x[1])
                if y not in dist: dist[y]=dist[x]+1; q.append(y)
        best=min(best,dist.get((s,1),10**9))
    return best
om=np.array([omega(A) for A in adj]); og=np.array([oddgirth(A) for A in adj])
out=[]; P=lambda s="": (print(s), out.append(s))
def turan(k,r):
    r=min(r,k); q,s=divmod(k,r); return comb(k,2)-s*comb(q+1,2)-(r-s)*comb(q,2)
# ---- (3) closed forms
P("## (3) closed forms on 1276 cores")
bad=0; tot=0
for k in range(2,10):
    t=ix[f"K{k}"]
    for g in range(N):
        tot+=1; bad+= a[t,g]!=comb(k,2)-turan(k,om[g])
P(f"- alpha(K_k,G) = C(k,2) - t(k,min(k,omega)) for k=2..9: {tot-bad}/{tot} entries agree")
bad=0; tot=0; vals=set()
for c in ["C5","C7","C9","C11"]:
    L=int(c[1:]); t=ix[c]
    for g in range(N):
        tot+=1; exp=0 if og[g]<=L else 1; vals.add(a[t,g]); bad+= a[t,g]!=exp
P(f"- alpha(C_(2k+1),G) in {{0,1}} with 0 iff og(G) <= 2k+1, for C5..C11: {tot-bad}/{tot} agree; values seen {sorted(vals)}")
P(f"- alpha(Petersen,C5) = {a[ix['Petersen'],ix['C5']]:.0f} (phi = {a[ix['Petersen'],ix['C5']]/15:.4f} = 2/15)")
# ---- (1b) psi
P("\n## (1b) source-side profile psi(G)_T = max_{X->G, X in pool} alpha(X,T)/e(X), T in K2..K5")
KT=[ix[f"K{k}"] for k in range(2,6)]
maps=(a==0)  # maps[X,G]: X->G
def psi(pool):
    S=np.zeros((N,4))
    for j,t in enumerate(KT):
        v=a[pool,t]/m[pool]   # alpha(X,T)/e(X)
        M=np.where(maps[pool,:], v[:,None], -1).max(0); S[:,j]=np.maximum(M,0)
    return S
def chi_from(S):
    # chi_hat = smallest k in 2..5 with psi_{K_k}=0, else ">=6"
    out=np.full(N,6)
    for j in range(3,-1,-1):
        out[S[:,j]==0]=j+2
    return out
chi_c=np.minimum(chi,6)
P("| pool of sources X | |pool| | chi recovered exactly (chi capped at 6) | errors by true chi |")
P("|---|---|---|---|")
pools=[("all 1276 cores (G itself included)",np.arange(N)),("85 cores (n<=8 + named)",np.array([ix[l] for l in mat(R/'alpha.csv')[0]])),
       ("B12",np.array([ix[l] for l in ["K2","K3","K4","K5","K6","C5","C7","C9","Petersen","Grotzsch","W5","Icosahedron"]]))]+\
      [(f"cores with n<={k}",np.where(n<=k)[0]) for k in (5,6,7,8)]
for name,pool in pools:
    ch=chi_from(psi(pool)); ok=(ch==chi_c)
    errs={int(c):int((~ok&(chi==c)).sum()) for c in sorted(set(chi)) if (~ok&(chi==c)).sum()}
    P(f"| {name} | {len(pool)} | {ok.sum()}/{N} | {errs} |")
# ---- (2) recommendation numbers: extra variants
P("\n## (2) extra variants (targets = 1276 cores)")
dist=mat(D/"dist_n9.csv")[1]; dstar=mat(D/"dist_closure_n9.csv")[1]; dn=mat(D/"dnorm_n9.csv")[1]
iu=np.triu_indices(N,1); X=(a/m[:,None]).T
def E(cols,w):
    Y=X[:,cols]*w; sq=(Y**2).sum(1); return np.sqrt(np.maximum(sq[:,None]+sq[None,:]-2*Y@Y.T,0))
def chiw(cols, cap=None):
    c=chi[cols]; return np.array([1/np.sqrt((c==x).sum()) for x in c])
lab85=mat(R/'alpha.csv')[0]; c85=np.array([ix[l] for l in lab85]); call=np.arange(N)
B=np.array([ix[l] for l in ["K2","K3","K4","K5","K6","C5","C7","C9","Petersen","Grotzsch","W5","Icosahedron"]])
fams=[("all 1276, unweighted",call,np.ones(N)),("all 1276, chi-balanced",call,chiw(call)),
      ("85 tests, unweighted",c85,np.ones(len(c85))),("85 tests, chi-balanced",c85,chiw(c85)),
      ("B12, chi-balanced",B,chiw(B)),
      ("all 1276, w=1/e(T)",call,1/m),("all 1276, chi-bal * 1/sqrt(e(T))",call,chiw(call)/np.sqrt(m))]
P("| tests, weights | E~dist P/S | E~d* P/S | E~d_n P/S | pairs E=0 | Spearman vs all-chi-bal |")
P("|---|---|---|---|---|---|")
ref=None
res={}
for name,cols,w in fams:
    e=E(cols,w)[iu]; res[name]=e
for name,cols,w in fams:
    e=res[name]; r=[]
    for M in (dist,dstar,dn):
        x=M[iu]; r.append(f"{np.corrcoef(e,x)[0,1]:.3f}/{spearmanr(e,x)[0]:.3f}")
    P(f"| {name} | {' | '.join(r)} | {(e<1e-12).sum()} | {spearmanr(e,res['all 1276, chi-balanced'])[0]:.3f} |")
# stability of chi-balanced 85-test family on 1276 targets: leave-one-out
w85=chiw(c85); base=rankdata(res["85 tests, chi-balanced"]); rh=[]
for k in range(len(c85)):
    keep=np.arange(len(c85))!=k; cols=c85[keep]
    rh.append(np.corrcoef(base,rankdata(E(cols,chiw(cols))[iu]))[0,1])
P(f"\n85 tests chi-balanced, leave-one-test-out (weights recomputed): min rho {min(rh):.4f}, median {np.median(rh):.4f}, worst = {lab85[int(np.argmin(rh))]}")
open(pathlib.Path(__file__).parent/"Q_round2_out.md","w").write("\n".join(out)+"\n")
