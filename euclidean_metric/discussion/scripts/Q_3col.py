import sys, time
E=[tuple(map(int,l.split())) for l in open(sys.argv[1])]
n=max(max(e) for e in E)+1; adj=[set() for _ in range(n)]
for u,v in E: adj[u].add(v); adj[v].add(u)
dom=[{0,1,2} for _ in range(n)]; dom[0]={0}; nodes=0
def solve(dom):
    global nodes; nodes+=1
    un=[v for v in range(n) if len(dom[v])>1]
    if not un: return True
    v=min(un,key=lambda x:(len(dom[x]),-len(adj[x])))
    for c in sorted(dom[v]):
        d=[set(s) for s in dom]; d[v]={c}; stack=[v]; ok=True
        while stack and ok:
            x=stack.pop()
            if len(d[x])==1:
                cx=next(iter(d[x]))
                for y in adj[x]:
                    if cx in d[y]:
                        d[y].discard(cx)
                        if not d[y]: ok=False; break
                        if len(d[y])==1: stack.append(y)
        if ok and solve(d): return True
    return False
t=time.time(); r=solve(dom); print("3-colourable:",r,"nodes",nodes,f"{time.time()-t:.1f}s")
