import numpy as np, sys, csv
sys.argv=['x']
import R_analysis as R
import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
SL=["#2a78d6","#eb6834","#1baf7a","#eda100","#e87ba4","#008300","#6250d6","#e34948"]
lab,X,chi,gs=R.load("_n9"); N=len(lab); I=lab.index
A=(X.T)  # A[S,G]=alpha(S,G)/e(S)
inv=[R.invariants(R.g6(s)) for s in gs]; om=np.array([v['omega'] for v in inv]); chif=np.array([v['chif'] for v in inv])
def chiw(cols): return np.array([1/np.sqrt((chi[cols]==chi[t]).sum()) for t in cols])
w=chiw(np.arange(N)); Xw=X*w
Yw,vw,Vtw,muw=R.pca(Xw)
print("chi-balanced 1276: var",np.round(vw[:5],3))
for p in range(4):
    cs={k:np.corrcoef(Yw[:,p],v)[0,1] for k,v in dict(chi=chi*1.,omega=om*1.,chif=chif,trifree=(om==2)*1.).items()}
    top=np.argsort(-np.abs(Vtw[p]))[:4]
    print(f" PC{p+1}",{k:round(c,2) for k,c in cs.items()},[(lab[t],round(Vtw[p,t],2)) for t in top])
print(" PC1 loadings sign", Vtw[0].min().round(3), Vtw[0].max().round(3))
# order check for weighted PC1
hom=(A==0)  # hom[S,G]: S->G  (phi(G)_S==0)
s=np.sign(Vtw[0].sum()); P1=s*Yw[:,0]
viol=sum(1 for g in range(N) for h in np.where(hom[g])[0] if h!=g and P1[g]<=P1[h]+1e-12)
print(" weighted PC1 order violations:",viol,"of",hom.sum()-N)
# chi separation in weighted space: LOO nearest-centroid / 1-NN
D=np.sqrt(((Xw[:,None]-Xw[None])**2).sum(-1)); np.fill_diagonal(D,np.inf)
print(" 1-NN same chi (weighted): %.3f, same omega %.3f"%((chi[D.argmin(1)]==chi).mean(),(om[D.argmin(1)]==om).mean()))
Du=np.sqrt(((X[:,None]-X[None])**2).sum(-1)); np.fill_diagonal(Du,np.inf)
print(" 1-NN same chi (unweighted): %.3f"%((chi[Du.argmin(1)]==chi).mean()))
# ---- psi: psi(G)_T = max_{X->G} alpha(X,T)/e(X), X over the 1276 cores
psi=np.zeros((N,N))
for g in range(N):
    src=np.where(hom[:,g])[0]   # X with X->G
    psi[g]=A[src].max(0)       # A[X,T]=alpha(X,T)/e(X)
raw=A.copy()  # raw source profile alpha(G,T)/e(G) = A[G,:]
print("\npsi: fraction of entries where psi > raw source profile: %.3f"%((psi>raw+1e-12).mean()))
# chi exactly from psi
kk=[I(f"K{k}") for k in range(2,10)]
chi_from_psi=np.array([2+min(j for j,k in enumerate(kk) if psi[g,k]==0) for g in range(N)])
print("chi(G)=min{k: psi_Kk=0} exact:",(chi_from_psi==chi).all())
# monotone: G->H => psi(G)<=psi(H)
bad=sum(1 for g in range(N) for h in np.where(hom[g])[0] if (psi[g]>psi[h]+1e-12).any()); print("psi monotonicity failures",bad)
n_phi=X.mean(1); n_psi=psi.mean(1)
# separation of chi classes by (||phi||,||psi||): 1-NN in this 2D plane and in concat space
Z=np.column_stack([n_phi,n_psi]); D2=np.sqrt(((Z[:,None]-Z[None])**2).sum(-1)); np.fill_diagonal(D2,np.inf)
print("2D (mean phi, mean psi): 1-NN same chi %.3f"%(chi[D2.argmin(1)]==chi).mean())
for c in sorted(set(chi)):
    s_=chi==c; print(f"  chi={c} (n={s_.sum()}): mean psi range [{n_psi[s_].min():.3f},{n_psi[s_].max():.3f}]  mean phi [{n_phi[s_].min():.3f},{n_phi[s_].max():.3f}]")
# linear separability of chi<=k in psi alone, in 2D, and in (phi,psi) restricted to 85 tests
from scipy.optimize import linprog
lab85=[r[1] for r in csv.reader(open(R.DATA/"cores_meta.csv"))][1:]; cols=[I(l) for l in lab85]
def sep(F,y):
    r=linprog(np.zeros(F.shape[1]+1),A_ub=-y[:,None]*np.column_stack([F,np.ones(len(y))]),b_ub=-np.ones(len(y)),bounds=(None,None),method='highs'); return r.status==0
for k in (2,3,4,5):
    y=np.where(chi<=k,1,-1)
    print(f"  chi<={k} separable: 2D norms {sep(Z,y)}, psi(85 tests) {sep(psi[:,cols],y)}, phi(85 tests) {sep(X[:,cols],y)}")
# ---- B12 + Q big graphs
B12=["K2","K3","K4","K5","K6","C5","C7","C9","Petersen","Grotzsch","W5","Icosahedron"]; bc=[I(b) for b in B12]
wb=chiw(np.array(bc)); XB=X[:,bc]*wb
YB,vB,VtB,muB=R.pca(XB)
Q=list(csv.DictReader(open("Q_profiles.csv")))
QX=np.array([[float(r["phi_"+b]) for b in B12] for r in Q])*wb; QY=(QX-muB)@VtB.T
Qnames=[r["target"] for r in Q]
print("\nB12 chi-balanced var",np.round(vB[:3],3))
np.savez("R2_cache.npz",Yw=Yw,vw=vw,YB=YB,vB=vB,QY=QY,Qnames=np.array(Qnames),n_phi=n_phi,n_psi=n_psi,chi=chi,om=om,lab=np.array(lab))
