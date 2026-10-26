import csv, numpy as np, pathlib
R=pathlib.Path("/home/rostam/kara/NonHomomorphism/open_problems/metric_space/data")
rows=list(csv.reader(open("Q_profiles_raw.csv"))); hdr=rows[0]; tests=hdr[3:-1]
m={"K2":1,"K3":3,"K4":6,"K5":10,"K6":15,"C5":5,"C7":7,"C9":9,"Petersen":15,"Grotzsch":20,"W5":10,"Icosahedron":30}
out=[]; P={}
for r in rows[1:]:
    vals=[]; note=""
    for t,v in zip(tests,r[3:-1]):
        if v.startswith("<="):
            # alpha(Ico,H)=10 for every triangle-free H with an edge: 20 faces, each edge in 2 -> >=10; alpha(Ico,K2)=10
            assert t=="Icosahedron" and r[3+tests.index("K3")]=="1"; v=v[2:]; note="Ico=10 by triangle-cover bound"
        vals.append(int(v))
    P[r[0]]=np.array(vals)/np.array([m[t] for t in tests])
    out.append([r[0],r[1],r[2]]+vals+[note])
# nearest n9 core (basis columns), via raw alpha_n9
rr=list(csv.reader(open(R/"alpha_n9.csv"))); lab=rr[0][1:]; a=np.array([[float(x) for x in q[1:]] for q in rr[1:]])
meta={q["label"]:q for q in csv.DictReader(open(R/"cores_meta_n9.csv"))}
idx=[lab.index(t) for t in tests]; mm=np.array([m[t] for t in tests])
X=a[idx,:].T/mm  # rows cores
with open("Q_profiles.csv","w") as f:
    w=csv.writer(f); w.writerow(["target","n","m"]+[f"alpha({t},G)" for t in tests]+[f"phi_{t}" for t in tests]+["n9_cores_same_profile","nearest_chi","note"])
    for o in out:
        p=P[o[0]]; d=np.sqrt(((X-p)**2).sum(1)); same=(d<1e-9).sum(); j=d.argmin()
        w.writerow(o[:3]+o[3:-1]+[f"{x:.4f}" for x in p]+[same, meta[lab[j]]["chi"], o[-1]])
        print(f"{o[0]:28s} {' '.join(str(x) for x in o[3:-1])}  same-profile n9 cores={same:4d} (e.g. {lab[j]}, chi={meta[lab[j]]['chi']})")
# collisions among big graphs
from collections import defaultdict
g=defaultdict(list)
for k,p in P.items(): g[tuple(np.round(p,6))].append(k)
print("\nprofile classes among targets:")
for k,v in g.items(): print(len(v), v)
