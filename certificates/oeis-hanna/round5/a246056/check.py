"""Exact checks for A246056: definition, mod-3 pattern, Lucas factorisation and the key identity."""
from math import comb
import json
from pathlib import Path, sys
N = 320
def mul(a,b,n):
    c=[0]*n
    for i,x in enumerate(a[:n]):
        if x:
            for j,y in enumerate(b[:n-i]):
                if y: c[i+j]+=x*y
    return c
def P(r,t,n):  # coefficients of P_r(t*x) truncated
    return [comb(r,k)**2 * t**k if k<=r else 0 for k in range(n)]
inv12=[2**k for k in range(N)]          # 1/(1-2x)
A=[0]*N
powcache=[1]+[0]*(N-1)                   # (1/(1-2x))^1 built incrementally
cur=inv12[:]                             # (1-2x)^{-(2r+1)} for r=0
for r in range(N):
    if r>0:
        cur=mul(mul(cur,inv12,N),inv12,N)
    term=mul(mul(P(r,2,N),P(r,3,N),N),cur,N)
    for k in range(N-r):
        A[r+k]+=term[k]
def ternary_only02(n):
    while n:
        if n%3==1: return False
        n//=3
    return True
bad=[n for n in range(N) if A[n]%3 != (1 if ternary_only02(n) else 0)]
# compare with b-file
bf={}
for line in open(Path(__file__).resolve().parents[2]/'bfiles'/'b246056.txt'):
    s=line.split()
    if len(s)>=2 and not line.startswith('#'):
        try: bf[int(s[0])]=int(s[1])
        except: pass
mism=[n for n in range(N) if n in bf and bf[n]!=A[n]]
# Lucas factorisation P_{3m+d}(t) = P_m(t^3) P_d(t) mod 3
luc_bad=[]
for m in range(0,12):
    for d in range(3):
        r=3*m+d
        lhs=[comb(r,k)**2 % 3 for k in range(r+1)]
        rhs=[0]*(r+1)
        for j in range(m+1):
            for e in range(d+1):
                rhs[3*j+e]=(rhs[3*j+e]+comb(m,j)**2*comb(d,e)**2)%3
        if lhs!=rhs: luc_bad.append(r)
# key identity: (1+x^3) * S(x) = 1 + x^2 mod 3, with S = sum_{d<3} x^d P_d(-x)/(1+x)^{2d+1}
# equivalently numerator: (1+x)^4 + x(1-x)(1+x)^2 + x^2(1-x+x^2) == (1+x^2)(1+x)^2 mod 3
import itertools
def polymul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c
lhs=[0]*6
for poly in [polymul(polymul([1,1],[1,1]),polymul([1,1],[1,1])), polymul([0,1,-1],polymul([1,1],[1,1])), polymul([0,0,1],[1,-1,1])]:
    for i,x in enumerate(poly): lhs[i]+=x
rhs=polymul([1,0,1],polymul([1,1],[1,1]))
ident_ok=[x%3 for x in lhs[:5]]==[x%3 for x in rhs[:5]]
res={"terms":N,"pattern_violations":bad[:10],"bfile_terms":len(bf),"bfile_mismatch":mism[:10],"lucas_failures":luc_bad,"key_identity_mod3":ident_ok,"first":A[:12]}
print(json.dumps(res)); json.dump(res,open(Path(__file__).with_name('check.json'),'w'))
