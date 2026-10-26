import numpy as np, sys
sys.argv=['x']; import R_analysis as R
import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
SL=["#2a78d6","#eb6834","#1baf7a","#eda100","#e87ba4","#008300","#6250d6","#e34948"]
d=np.load("R2_cache.npz"); lab=list(d["lab"]); chi=d["chi"]; I=lab.index
cs=sorted(set(chi)); col={c:SL[min(k,7)] for k,c in enumerate(cs)}
col[9]="#555555"
def style(a):
    for s in ("top","right"): a.spines[s].set_visible(False)
    a.grid(color="#e6e6e3",lw=.6); a.set_axisbelow(True)
def scat(a,x,y,leg=True):
    for c in cs:
        s=chi==c; a.scatter(x[s],y[s],s=14 if s.sum()>50 else 34,c=col[c],lw=.5,edgecolor="white",label=f"χ={c} ({s.sum()})",zorder=3 if s.sum()<50 else 2)
def ann(a,x,y,names=None,skip=()):
    for k,l in enumerate(lab):
        if R.is_named(l) and l not in skip: a.annotate(l,(x[k],y[k]),fontsize=8,color="#222",xytext=(4,2),textcoords="offset points",zorder=5)
fig,ax=plt.subplots(1,3,figsize=(21,7))
# (a) chi-balanced PCA
Y=d["Yw"]; v=d["vw"]; sg=-1 if Y[I("K9"),0]>Y[I("K2"),0] else 1
a=ax[0]; scat(a,sg*Y[:,0],Y[:,1]); ann(a,sg*Y[:,0],Y[:,1],skip=("C9","C11","C7")); style(a)
a.set_xlabel(f"PC1 ({v[0]:.0%}) — r = −0.93 with χ, −0.92 with ω (sign flipped: right = 'smaller' graphs)")
a.set_ylabel(f"PC2 ({v[1]:.0%})")
a.set_title("(a) φ = target profile, χ-balanced weights, 1276 cores n≤9\nPC1 is a strict height on the hom order (0 / 615k violations)",loc="left",fontsize=11)
a.legend(frameon=False,fontsize=8,loc="upper center",ncol=3)
# (b) norms
x=d["n_phi"]; y=d["n_psi"]
a=ax[1]; scat(a,x,y,False); style(a)
for k in range(3,9):
    yk=y[I(f"K{k}")]; a.axhline(yk,color="#999",lw=.7,ls="--",zorder=1); a.text(0.272,yk,f"‖ψ(K{k})‖",fontsize=7.5,color="#666",va="bottom",ha="right")
ann(a,x,y,skip=("K5","K6","K7","K8","K9","C9","C11","C7"))
a.set_xlabel("mean φ(G)  (what maps INTO G: governed by ω)"); a.set_ylabel("mean ψ(G)  (what G maps INTO: governed by χ)")
a.set_title("(b) Two profiles, two invariants: χ(G) ≤ k  ⇔  ‖ψ(G)‖ ≤ ‖ψ(K_k)‖\non all 1276 cores (ψ approximated by max over cores X→G)",loc="left",fontsize=11)
# (c) B12 + Q big graphs
YB=d["YB"]; vB=d["vB"]; QY=d["QY"]; Qn=list(d["Qnames"]); sb=-1 if YB[I("K9"),0]>YB[I("K2"),0] else 1
a=ax[2]; scat(a,sb*YB[:,0],YB[:,1]); style(a)
for k,l in enumerate(lab):
    if l in ("K2","K3","K4","K5","C5","Petersen","Grotzsch","Icosahedron","W5"): a.annotate(l,(sb*YB[k,0],YB[k,1]),fontsize=8,color="#222",xytext=(4,-9),textcoords="offset points")
show={"M5_Mycielski":"Mycielski M5","Clebsch":"Clebsch","Chvatal":"Chvátal","Kneser(8 3)":"Kneser(8,3)","Heawood":"Heawood","Dodecahedron":"Dodecahedron","Kneser(7 2)":"Kneser(7,2)","Paley13":"Paley13","Circ(13;1 5)":"Circ(13;1,5)","G(20 0.5)#1":"G(20,.5)"}
qx=sb*QY[:,0]; a.scatter(qx,QY[:,1],s=70,facecolor="none",edgecolor="#111",lw=1.1,zorder=4,label="larger graphs (Q, B12 only)")
seen=set()
for k,n in enumerate(Qn):
    if n in show:
        key=(round(qx[k],3),round(QY[k,1],3)); off=12 if key in seen else 0; seen.add(key)
        a.annotate(show[n],(qx[k],QY[k,1]),fontsize=8,color="#111",fontweight="bold",xytext=(6,6+off),textcoords="offset points")
a.set_xlabel(f"PC1 of B12 profile ({vB[0]:.0%})"); a.set_ylabel(f"PC2 ({vB[1]:.0%})")
a.set_title("(c) 12-test basis B12: big graphs land on small cores\nHeawood = K2, Dodecahedron = C5, G(20,.5) = K5; new points only triangle-free",loc="left",fontsize=11)
a.legend(frameon=False,fontsize=8,loc="lower left")
fig.suptitle("The α-profile space: one dominant 'height' axis (the hom order); the target profile φ reads ω, the source profile ψ reads χ",x=0.01,ha="left",fontsize=14)
fig.tight_layout(); fig.savefig("R_final.png",dpi=130)
