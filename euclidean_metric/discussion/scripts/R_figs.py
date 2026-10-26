import numpy as np, sys
sys.argv=['x']
import R_analysis as R
from scipy.cluster.hierarchy import linkage, fcluster, dendrogram
import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
SL=["#2a78d6","#eb6834","#1baf7a","#eda100","#e87ba4","#008300","#6250d6","#e34948"]
lab,X,chi,gs=R.load(""); N=len(lab); I=lab.index
inv=[R.invariants(R.g6(s)) for s in gs]; om=np.array([v['omega'] for v in inv])
Y,var,Vt,mu=R.pca(X)
col={c:SL[k] for k,c in enumerate(sorted(set(chi)))}
def style(ax):
    for s in ("top","right"): ax.spines[s].set_visible(False)
    ax.grid(color="#e6e6e3",lw=.6); ax.set_axisbelow(True)
def ann(ax,xs,ys,fs=8.5):
    for k,l in enumerate(lab):
        if R.is_named(l): ax.annotate(l,(xs[k],ys[k]),fontsize=fs,color="#333",xytext=(4,3),textcoords="offset points")
def scat(ax,xs,ys,mask=None):
    mask=np.ones(N,bool) if mask is None else mask
    for c in sorted(set(chi[mask])):
        s=mask&(chi==c); ax.scatter(xs[s],ys[s],s=40,c=col[c],edgecolor="white",lw=1.1,label=f"χ={c}",zorder=3)
# ---------- Fig 1: axes
hom=np.array([[X[h,g]==0 for h in range(N)] for g in range(N)])
covers=[(g,h) for g in range(N) for h in range(N) if g!=h and hom[g,h] and not any(k not in(g,h) and hom[g,k] and hom[k,h] for k in range(N))]
fig,ax=plt.subplots(1,3,figsize=(19,6.2))
a=ax[0]
for g,h in covers: a.plot([Y[g,1],Y[h,1]],[Y[g,0],Y[h,0]],color="#bbb",lw=.5,zorder=1)
scat(a,Y[:,1],Y[:,0]); ann(a,Y[:,1],Y[:,0]); style(a)
a.set_xlabel(f"PC2 ({var[1]:.0%})"); a.set_ylabel(f"PC1 ({var[0]:.0%})  ≈ ‖φ‖₁ (r = 0.9997)")
a.set_title("PC1 is a height function on the hom order\n(grey: Hasse covers G→H; every one points downward)",loc="left",fontsize=11)
a.legend(frameon=False,fontsize=8,loc="lower right")
m3=om>=3; Ys,vs,Vts,_=R.pca(X[m3]); xs=np.full(N,np.nan); ys=np.full(N,np.nan); xs[m3]=Ys[:,0]; ys[m3]=Ys[:,1]
a=ax[1]; scat(a,xs,ys,m3); ann(a,xs,ys); style(a)
a.set_xlabel(f"PC1 within ω≥3 ({vs[0]:.0%}; r=−0.85 with triangles/edge)"); a.set_ylabel(f"PC2 within ω≥3 ({vs[1]:.0%}; tests K4..K8)")
a.set_title("Triangle effect removed: cores with ω ≥ 3 only",loc="left",fontsize=11)
m2=om==2; Yt,vt,Vtt,_=R.pca(X[m2]); xs=np.full(N,np.nan); ys=np.full(N,np.nan); xs[m2]=Yt[:,0]; ys[m2]=Yt[:,1]
chif=np.array([v['chif'] for v in inv])
a=ax[2]; scat(a,xs,ys,m2); style(a)
for k in np.where(m2)[0]:
    a.annotate(f"{lab[k] if R.is_named(lab[k]) else ''} χf={chif[k]:.2f}".strip(),(xs[k],ys[k]),fontsize=8,color="#333",xytext=(4,3),textcoords="offset points")
a.set_xlabel(f"PC1 within triangle-free ({vt[0]:.0%}; r=+0.92 with χ_f)"); a.set_ylabel(f"PC2 ({vt[1]:.0%})")
a.set_title("Triangle-free cores: PC1 orders by fractional χ",loc="left",fontsize=11)
fig.tight_layout(); fig.savefig("R_axes.png",dpi=130)
# ---------- Fig 2: K3-K4 geometry + centroids
p,q=X[I('K3')],X[I('K4')]; dv=q-p; L=np.linalg.norm(dv)
t=(X-p)@dv/(dv@dv); perp=np.linalg.norm(X-(p+t[:,None]*dv),axis=1)
fig,ax=plt.subplots(1,2,figsize=(15,6))
a=ax[0]; sel=(t>-0.4)&(t<1.4)
scat(a,t,perp,sel); style(a)
for k,l in enumerate(lab):
    if R.is_named(l) and sel[k]: a.annotate(l,(t[k],perp[k]),fontsize=9,color="#333",xytext=(4,3),textcoords="offset points")
a.axvspan(0,1,color="#f3f3f0",zorder=0); a.plot([0,1],[0,0],color="#333",lw=2)
for c in sorted(set(chi)):
    cen=X[chi==c].mean(0); tc=(cen-p)@dv/(dv@dv); pc=np.linalg.norm(cen-(p+tc*dv))
    if -0.4<tc<1.4: a.scatter([tc],[pc],marker="X",s=110,c=col[c],edgecolor="#222",lw=.8,zorder=4); a.annotate(f"centroid χ={c}",(tc,pc),fontsize=8,xytext=(5,-10),textcoords="offset points")
a.set_xlabel("position t along segment K3 (t=0) → K4 (t=1)"); a.set_ylabel("distance to the line K3K4")
a.set_title(f"Straight line K3→K4 (length {L:.2f}): cores sit near the ends, the middle is empty\n(nearest core to the midpoint is 0.29 away; X = χ-class centroids)",loc="left",fontsize=11)
a.legend(frameon=False,fontsize=8,loc="upper left")
# panel b: centroid distances
a=ax[1]; style(a)
cl=sorted(set(chi)); D=[]; 
for c in cl:
    cen=X[chi==c].mean(0); d=np.linalg.norm(X-cen,axis=1); D.append((c,(chi==c).sum(),d.min(),d[chi==c].mean(),lab[int(np.argmin(d))]))
xs=np.arange(len(cl))
a.bar(xs-0.2,[x[3] for x in D],0.38,color="#c9c9c4",label="mean distance of class members to centroid")
a.bar(xs+0.2,[x[2] for x in D],0.38,color=[col[c] for c in cl],label="distance from centroid to nearest real core")
for i,x in enumerate(D): a.annotate(f"{x[4]}\n(n={x[1]})",(xs[i]+0.2,x[2]),ha="center",fontsize=8,xytext=(0,3),textcoords="offset points")
a.set_xticks(xs,[f"χ={c}" for c in cl]); a.set_ylabel("E distance"); a.legend(frameon=False,fontsize=8)
a.set_title("'Average graph' of each χ-class and the real core nearest to it",loc="left",fontsize=11)
fig.tight_layout(); fig.savefig("R_geometry.png",dpi=130)
# ---------- Fig 3: clusters
fig,ax=plt.subplots(1,2,figsize=(17,6.2),gridspec_kw={"width_ratios":[1.3,1]})
Lk=linkage(X,"ward")
dn=dendrogram(Lk,ax=ax[0],labels=[l if R.is_named(l) else "" for l in lab],leaf_font_size=8,color_threshold=Lk[-6,2],above_threshold_color="#999")
ax[0].set_title("Ward clustering of the 85 cores in E (6 clusters coloured)\nsplits: ω=2 | ω=3 (three groups) | ω≥4; triangle-free splits into {K2,long odd cycles} vs {C5,Petersen,Grötzsch}",loc="left",fontsize=10.5)
for s in ("top","right"): ax[0].spines[s].set_visible(False)
lab9,X9,chi9,gs9=R.load("_n9"); Y9,var9,_,_=R.pca(X9); c9=fcluster(linkage(X9,"ward"),4,"maxclust")
names={}
for c in set(c9):
    s=c9==c; ch=np.bincount(chi9[s]).argmax(); names[c]=s.sum()
order=sorted(set(c9),key=lambda c:-names[c])
desc={}
a=ax[1]; style(a)
for k,c in enumerate(order):
    s=c9==c; a.scatter(Y9[s,0],Y9[s,1],s=10,c=SL[k],lw=0,alpha=.8,label=f"cluster {k+1} ({s.sum()})")
for k,l in enumerate(lab9):
    if R.is_named(l): a.annotate(l,(Y9[k,0],Y9[k,1]),fontsize=8,color="#333",xytext=(3,2),textcoords="offset points")
a.legend(frameon=False,fontsize=8,title="718: ω=3, W5↛G | 301: ω≥4\n241: ω=3, W5→G | 16: triangle-free",title_fontsize=8)
a.set_xlabel(f"PC1 ({var9[0]:.0%})"); a.set_ylabel(f"PC2 ({var9[1]:.0%})")
a.set_title("1276 cores (n≤9): Ward k=4 = up-sets of the hom order",loc="left",fontsize=11)
fig.tight_layout(); fig.savefig("R_clusters.png",dpi=130)
print(len(covers),"covers")
