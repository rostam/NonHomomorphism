import numpy as np, sys
sys.argv=['x']
import R_analysis as R
from scipy.cluster.hierarchy import linkage, fcluster
from scipy.optimize import linprog
lab,X,chi,gs=R.load(""); N=len(lab)
a = X.T  # a[T,G]=phi(G)_T
Y,var,Vt,mu=R.pca(X)
print("PC1 loadings sign: min %.3f max %.3f"%(Vt[0].min(),Vt[0].max()))
# hom relation: G->H iff phi(H)_G == 0 (G is a test)
hom = np.array([[X[h,g]==0 for h in range(N)] for g in range(N)])  # hom[g,h]: g->h
viol=[(lab[g],lab[h]) for g in range(N) for h in range(N) if hom[g,h] and g!=h and Y[g,0]<Y[h,0]-1e-12]
print("pairs G->H, G!=H:",hom.sum()-N," PC1 order violations:",len(viol), viol[:5])
s1=X.sum(1); print("l1 norm violations:", sum(1 for g in range(N) for h in range(N) if hom[g,h] and g!=h and s1[g]<=s1[h]))
print("corr(PC1, ||phi||_1)=%.4f"%np.corrcoef(Y[:,0],s1)[0,1])
# monotonicity check phi(H)<=phi(G) coordinatewise if G->H
bad=sum(1 for g in range(N) for h in range(N) if hom[g,h] and (X[h]>X[g]+1e-12).any()); print("monotonicity failures",bad)
# K3-K4 midpoint
I=lab.index; mid=(X[I('K3')]+X[I('K4')])/2; d=np.linalg.norm(X-mid,axis=1); j=np.argsort(d)[:4]
print("K3K4 midpoint nearest", [(lab[x],round(d[x],3)) for x in j], "half-length", np.linalg.norm(X[I('K3')]-X[I('K4')])/2)
t,dd=None,None
p,q=X[I('K3')],X[I('K4')];dv=q-p;tt=(X-p)@dv/(dv@dv); dist=np.linalg.norm(X-(p+np.clip(tt,0,1)[:,None]*dv),axis=1)
inside=[(lab[k],round(tt[k],2),round(dist[k],3)) for k in range(N) if 0.15<tt[k]<0.85]; print("cores projecting to interior t in (.15,.85):",sorted(inside,key=lambda z:z[2])[:8])
print("t hist", np.histogram(tt,bins=[-1,0,.1,.3,.5,.7,.9,1,2])[0])
# where do the triangle-free/omega=3 cores with chi=4 project
for l in ['W5','W7','Icosahedron','Grotzsch','Petersen','C5']: k=I(l); print(l,'t=%.2f d=%.3f'%(tt[k],dist[k]))
# n9: what separates the 241 vs 718 omega=3 clusters
lab9,X9,chi9,gs9=R.load("_n9"); cl=fcluster(linkage(X9,'ward'),4,'maxclust')
sizes={c:(cl==c).sum() for c in set(cl)}; c241=[c for c in sizes if sizes[c]==241][0]; c718=[c for c in sizes if sizes[c]==718][0]
A,B=X9[cl==c241],X9[cl==c718]; diff=A.mean(0)-B.mean(0); top=np.argsort(-np.abs(diff))[:8]
print("241 vs 718 separating tests:",[(lab9[t],round(A[:,t].mean(),3),round(B[:,t].mean(),3)) for t in top])
for t in top[:3]:
    print(lab9[t],"frac zero (T->G) in 241: %.2f, in 718: %.2f"%((A[:,t]==0).mean(),(B[:,t]==0).mean()))
inv=[R.invariants(R.g6(s)) for s in gs9]
for k in ['n','m','dens','tri_per_edge','chif','maxdeg']:
    v=np.array([x[k] for x in inv],float); print(k, round(v[cl==c241].mean(),3), round(v[cl==c718].mean(),3))
# n9 linear separability of chi<=k with 85-test features
cols=[lab9.index(l) for l in lab]; F=X9[:,cols]; n9=len(lab9)
for k in (2,3,4,5):
    s=np.where(chi9<=k,1,-1); r=linprog(np.zeros(F.shape[1]+1),A_ub=-s[:,None]*np.column_stack([F,np.ones(n9)]),b_ub=-np.ones(n9),bounds=(None,None),method='highs')
    s2=r.status==0
    r=linprog(np.zeros(X9.shape[1]+1),A_ub=-s[:,None]*np.column_stack([X9,np.ones(n9)]),b_ub=-np.ones(n9),bounds=(None,None),method='highs')
    print(f"n9 chi<={k} separable: 85 tests {s2}, all 1276 tests {r.status==0}")
# n9 extreme points full-dim (LP 1276 vars) -- theorem predicts all
Y9,var9,Vt9,_=R.pca(X9); print("n9 PC1 loadings min/max %.3f %.3f"%(Vt9[0].min(),Vt9[0].max()))
