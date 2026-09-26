"""Sign-matrix inequality check: max_Y ||T_a(p) Y T_b(q)^T||_1 vs d_a(p) d_b(q) (Jiang-Yang Lemma 4.1)."""
import subprocess, sys, json
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from icg_model import T, dpoly, matmul, transpose
BIN = Path(__file__).parent / 'icg_sign'
def run(a,b,p,q,workers=12):
    nc=(a+1)*(b+1); pb=min(nc,8) if nc>20 else 0; npre=1<<pb
    chunks=[(k*npre//workers,(k+1)*npre//workers) for k in range(workers)] if pb else [(0,1)]
    chunks=[c for c in chunks if c[0]<c[1]]
    def job(c):
        out=subprocess.run([str(BIN),str(a),str(b),str(p),str(q),str(pb),str(c[0]),str(c[1])],capture_output=True,text=True,check=True).stdout
        return [tuple(map(int,l.split())) for l in out.split('\n') if l.strip()]
    with ThreadPoolExecutor(len(chunks)) as ex: res=[r for part in ex.map(job,chunks) for r in part]
    res.sort(reverse=True); return res
def signY(mask,a,b):
    return [[1 if mask>>(i*(b+1)+j)&1 else -1 for j in range(b+1)] for i in range(a+1)]
a,b,q=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])
for p in [int(t) for t in sys.argv[4].split(',')]:
    res=run(a,b,p,q)
    bound=dpoly(a,p)*dpoly(b,q)
    M=T(a,p);N=T(b,q)
    for e,m in res[:4]:
        Y=signY(m,a,b); Z=matmul(matmul(M,Y),transpose(N)); assert sum(abs(v) for r in Z for v in r)==e
    # distinct values
    vals=sorted(set(e for e,m in res),reverse=True)
    print(json.dumps(dict(a=a,b=b,p=p,q=q,bound=bound,max=res[0][0],excess=res[0][0]-bound,second_value=vals[1] if len(vals)>1 else None,top=[(e,m) for e,m in res[:4]])))
    if res[0][0]>=bound:
        for e,m in res[:4]:
            if e>=bound: print('   Y=',signY(m,a,b),e)
