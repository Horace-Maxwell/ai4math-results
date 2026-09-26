"""Independent q=3 certificate, derived from numerical Möbius Ramanujan sums.

No Ramanujan matrix or polynomial coefficient file is imported from the first
implementation. Interpolate each weighted basis term at p=5,7,11, after deriving
the degree <=2 bound from the prime-power formula. Spectral multiplicities are
also independently counted by gcd(j,n), j=0,...,n-1.
"""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import gcd
from pathlib import Path
import hashlib,json,time

@lru_cache(None)
def divisors(n): return [d for d in range(1,n+1) if n%d==0]
@lru_cache(None)
def mobius(n):
    count=0
    d=2
    while d*d<=n:
        if n%d==0:
            n//=d;count+=1
            if n%d==0:return 0
        d+=1
    if n>1:count+=1
    return (-1)**count
def ramanujan(j,m):return sum(d*mobius(m//d) for d in divisors(gcd(j,m)))
def phi(n):return sum(gcd(j,n)==1 for j in range(1,n+1))
def interp(v):
    # values at t=0,2,6, where t=p-5
    a=Fraction(v[0]); c=(Fraction(v[2]-v[0],6)-Fraction(v[1]-v[0],2))/4
    b=Fraction(v[1]-v[0],2)-2*c
    assert all(x.denominator==1 for x in (a,b,c))
    return [int(x) for x in (a,b,c)]
def ev(c,t):return c[0]+c[1]*t+c[2]*t*t

start=time.monotonic()
pairs=list(product(range(3),range(4)))
dpairs=pairs[:-1]
star={(0,0),(0,2),(1,1),(1,3),(2,0),(2,2)}
star_mask=sum(1<<i for i,d in enumerate(dpairs) if d in star)
samples=[]
for p in (5,7,11):
    n=p*p*27
    multiplicities=Counter(gcd(j,n) for j in range(n))
    assert set(multiplicities)==set(divisors(n))
    assert all(v==phi(n//e) for e,v in multiplicities.items())
    samples.append([[multiplicities[p**a*3**b]*ramanujan(p**a*3**b,n//(p**c*3**d))
                    for c,d in dpairs] for a,b in pairs])
terms=[[interp([samples[z][row][col] for z in range(3)]) for col in range(11)] for row in range(12)]
def rows(mask):return [[sum(terms[r][c][k] for c in range(11) if mask&(1<<c)) for k in range(3)] for r in range(12)]
star_rows=rows(star_mask)
assert all(all(v>=0 for v in row) or all(v<=0 for v in row) for row in star_rows)
target=[sum(abs(row[k]) for row in star_rows) for k in range(3)]
minimum=[10**12]*3
argmins=[[] for _ in range(3)]
for mask in range(2048):
    bound=[sum(abs(row[k]) for row in rows(mask)) for k in range(3)]
    gap=[a-b for a,b in zip(target,bound)]
    assert all(v>=0 for v in gap),(mask,gap)
    if mask!=star_mask:
        assert gap[0]>0,(mask,gap)
        for k,value in enumerate(gap):
            if value<minimum[k]:minimum[k]=value;argmins[k]=[mask]
            elif value==minimum[k]:argmins[k].append(mask)
for p in (13,17,31):
    n=p*p*27
    for a,b in pairs:
        r=pairs.index((a,b));e=p**a*3**b
        for c,d in dpairs:
            col=dpairs.index((c,d))
            direct=phi(n//e)*ramanujan(e,n//(p**c*3**d))
            assert ev(terms[r][col],p-5)==direct
out={'domain':'q=3, p>=5; graph interpretation requires p prime',
     'checked_masks':2048,'nonempty_masks':2047,'nonempty_competitors':2046,
     'star_mask':star_mask,'pairs':dpairs,'star_rows':star_rows,
     'target_coefficients_in_p_minus_5':target,'minimum_gap':minimum,
     'argmin_masks':argmins,'numeric_interpolation_primes':[5,7,11],
     'extra_basis_check_primes':[13,17,31],
     'method':'independent Mobius divisor-sum; gcd multiplicities; exact interpolation',
     'runtime_seconds':time.monotonic()-start}
dest=Path(__file__).with_name('independent_q3_certificate.json')
dest.write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
print('script sha256',hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
