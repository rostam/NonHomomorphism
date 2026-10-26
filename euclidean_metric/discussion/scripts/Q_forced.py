import csv, numpy as np, pathlib
R=pathlib.Path("/home/rostam/kara/NonHomomorphism/open_problems/metric_space/data")
for suf in ["","_n9"]:
    rows=list(csv.reader(open(R/f"alpha{suf}.csv"))); lab=rows[0][1:]
    a=np.array([[int(float(x)) for x in r[1:]] for r in rows[1:]],dtype=np.int16)
    A=a.T  # A[G,T]
    N=len(lab); forced=set(); nsep=[]; selfonly=0
    for i in range(N):
        D=(A[i][None,:]!=A[i+1:])  # pairs (i,j>i) x tests
        c=D.sum(1); nsep+=list(c)
        for jj in np.where(c==1)[0]:
            t=int(np.where(D[jj])[0][0]); forced.add(t)
            if t in (i,i+1+jj): selfonly+=1
    nsep=np.array(nsep)
    print(suf or "_n8", "pairs",len(nsep),"min #separating tests",nsep.min(),"pairs with exactly 1:",(nsep==1).sum(),
          "(of which the test is G or H itself:",selfonly,") forced tests:",len(forced), "median #sep tests", np.median(nsep))
    # greedy hitting set lower bound check: forced set alone separates how many?
    S=sorted(forced); X=A[:,S]
    _,cnt=np.unique(X,axis=0,return_counts=True); print("  forced set leaves merged pairs:", int((cnt*(cnt-1)//2).sum()))
    lab_=np.unique(X,axis=0,return_inverse=True)[1].ravel(); chosen=list(S)
    def ps(l):
        _,c=np.unique(l,return_counts=True); return int((c*(c-1)//2).sum())
    while ps(lab_)>0:
        best=None
        for t in range(N):
            if t in chosen: continue
            nl=np.unique(np.stack([lab_,A[:,t]],1),axis=0,return_inverse=True)[1].ravel()
            p=ps(nl)
            if best is None or p<best[0]: best=(p,t,nl)
        chosen.append(best[1]); lab_=best[2]
    print("  forced + greedy completion size:", len(chosen), "added:", [lab[t] for t in chosen[len(S):]])
    print("  forced tests chi distribution:", np.unique([0]*0+[int(x) for x in []]) if False else "")
