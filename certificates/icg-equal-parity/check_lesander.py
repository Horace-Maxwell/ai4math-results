# Sanity check: is Le-Sander's multiplicative maximum (a lower bound for E_max) sharp for n = p q^m?
from math import gcd
from itertools import combinations
from fractions import Fraction
def factor(n):
    f={};d=2
    while d*d<=n:
        while n%d==0: f[d]=f.get(d,0)+1; n//=d
        d+=1
    if n>1: f[n]=f.get(n,0)+1
    return f
def phi(n):
    r=n
    for p in factor(n): r=r//p*(p-1)
    return r
def mu(n):
    f=factor(n)
    return 0 if any(e>1 for e in f.values()) else (-1)**len(f)
def ram(k,m):  # Ramanujan sum c_m(k)
    g=gcd(k,m); return mu(m//g)*phi(m)//phi(m//g)
def energy(n,D):
    divs=[d for d in range(1,n+1) if n%d==0]
    E=0
    for g in divs:              # eigenvalue depends only on gcd(k,n)=g; multiplicity phi(n/g)
        lam=sum(ram(g,n//d) for d in D)
        E+=abs(lam)*phi(n//g)
    return E
def theta(p,s):
    if s%2: return Fraction((s+1)*(p*p-1)*p**s+2*(p**(s+1)-1),(p+1)**2)
    return Fraction(s*(p*p-1)*p**s+2*(2*p**(s+1)-p**(s-1)+p*p-p-1),(p+1)**2)
for (p,q,m) in [(5,3,1),(5,3,3),(3,5,3),(7,3,3),(3,7,3)]:
    n=p*q**m
    divs=[d for d in range(1,n) if n%d==0]
    best=0;arg=[]
    for r in range(1,len(divs)+1):
        for D in combinations(divs,r):
            e=energy(n,D)
            if e>best: best=e;arg=[D]
            elif e==best: arg.append(D)
    lt=theta(p,1)*theta(q,m)
    print(f"n={p}*{q}^{m}={n}: E_max(brute)={best}  LeSander multiplicative max={lt}  sharp={best==lt}  maximisers={arg}")
