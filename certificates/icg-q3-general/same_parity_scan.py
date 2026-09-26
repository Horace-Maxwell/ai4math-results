"""Exploratory scan: maximisers for same-parity exponents n=p^a q^b (exact, exhaustive via C)."""
import subprocess, json
from icg_model import energy, mask_to_X, dpoly
def run(a,b,p,q,W=12):
    nc=(a+1)*(b+1)-1; pb=min(nc,8) if nc>20 else 0; npre=1<<pb
    import concurrent.futures as cf
    chunks=[(k*npre//W,(k+1)*npre//W) for k in range(W)] if pb else [(0,1)]
    chunks=[c for c in chunks if c[0]<c[1]]
    def job(c):
        out=subprocess.run(['./icg_search',str(a),str(b),str(p),str(q),str(pb),str(c[0]),str(c[1])],capture_output=True,text=True,check=True).stdout
        return [tuple(map(int,l.split())) for l in out.split('\n') if l.strip()]
    with cf.ThreadPoolExecutor(len(chunks)) as ex: res=[r for part in ex.map(job,chunks) for r in part]
    res.sort(reverse=True); return res
def fmt(X): return '/'.join(''.join(str(v) for v in r) for r in X)
for (a,b) in [(1,1),(2,2),(1,3),(3,1),(3,3),(2,4),(4,2),(4,4),(1,5),(3,5)]:
    for (p,q) in [(3,5),(5,3),(3,7),(7,3),(5,7),(7,5),(5,11),(11,13),(13,11),(3,11)]:
        if (a+1)*(b+1)-1>29: continue
        res=run(a,b,p,q)
        e0,m0=res[0]; X=mask_to_X(m0,a,b)
        ties=sum(1 for e,m in res if e==e0)
        bound=(p**a*q**b+dpoly(a,p)*dpoly(b,q))//2
        print(f"a={a} b={b} p={p} q={q}: Emax={e0} (JY-type bound {bound}, deficit {bound-e0}) ties={ties} X={fmt(X)} second={res[1][0]}")
