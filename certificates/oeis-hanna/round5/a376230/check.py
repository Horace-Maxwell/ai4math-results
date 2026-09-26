"""Exact checks for A376230: recursion from A^2 = A(xA + xA^2 + xA^3), parity pattern (corrected), literal counterexample."""
import json, glob
from pathlib import Path
NEX = 48
def mul(a,b,n):
    c=[0]*n
    for i,x in enumerate(a[:n]):
        if x:
            for j,y in enumerate(b[:n-i]):
                if y: c[i+j]+=x*y
    return c
def compose(A,G,n):   # A(G) truncated, A[0]=0, G[0]=0; Horner
    res=[0]*n
    for k in range(len(A)-1,0,-1):
        res=[ (res[i] if i<n else 0) for i in range(n)]
        res[0]+=A[k]
        res=mul(res,G,n)
    return res
A=[0]*(NEX+2); A[1]=1
for n in range(2,NEX+1):
    m=n+2
    A2=mul(A,A,m); A3=mul(A2,A,m)
    G=[0]+[A[i]+A2[i]+A3[i] for i in range(m-1)]   # x*(A+A^2+A^3)
    AG=compose(A[:m],G,m)
    A[n]=AG[n+1]-A2[n+1]
exact=A[1:NEX+1]
# verify the equation holds up to degree NEX+1
m=NEX+2
A2=mul(A,A,m); A3=mul(A2,A,m); G=[0]+[A[i]+A2[i]+A3[i] for i in range(m-1)]
AG=compose(A[:m],G,m)
eq_ok=all(AG[i]==A2[i] for i in range(NEX+2))
bfpath=[str(Path(__file__).resolve().parents[2]/'bfiles'/'b376230.txt')]
bf={}
if bfpath:
    for line in open(bfpath[0]):
        s=line.split()
        if len(s)>=2 and not line.startswith('#'):
            try: bf[int(s[0])]=int(s[1])
            except: pass
mism=[n for n in range(1,NEX+1) if n in bf and bf[n]!=A[n]]
def inM(q):
    while q:
        if q%4>1: return False
        q//=4
    return True
def corrected(n): return n%8<4 and inM(n//8)
def literal(n): return n%4<4 and inM(n//4)   # n = 4*m + r, r in 0..3, m in Moser set
src = bf if bf else {n:A[n] for n in range(1,NEX+1)}
viol_corr=[n for n in sorted(src) if n>=1 and (src[n]%2==1)!=corrected(n)]
viol_lit=[n for n in sorted(src) if n>=1 and (src[n]%2==1)!=literal(n)]
res={"exact_terms":NEX,"equation_holds_to_degree":NEX+1 if eq_ok else None,"bfile_terms":len(bf),"exact_vs_bfile_mismatch":mism,
     "parity_checked_terms":len(src),"corrected_violations":viol_corr[:10],"literal_violations_first":viol_lit[:8],"a(1..12)":A[1:13]}
print(json.dumps(res)); json.dump(res,open(Path(__file__).with_name('check.json'),'w'))
