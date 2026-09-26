"""Independent integer-only polynomial certificate; no symbolic algebra package.

Polynomial arrays are low-degree first. Bivariate coefficient index is 4*i+j.
Input is the pair of Ramanujan factor tables and totient weights in Roldan,
arXiv:2604.09491v1 equations (8),(9). All arithmetic is exact Python integers.
"""
from itertools import product
from math import comb
from pathlib import Path
import json, csv, hashlib, time

BASE=Path(__file__).parent
def add(a,b):
    return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
def mul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,v in enumerate(a):
        for j,w in enumerate(b):out[i+j]+=v*w
    return out
def shift3(a,size):
    assert all(v==0 for v in a[size:])
    return [sum(a[k]*comb(k,i)*3**(k-i) for k in range(i,len(a))) for i in range(size)]
def ev1(a,v):return sum(c*v**i for i,c in enumerate(a))
def ev2(a,x,y):return sum(a[4*i+j]*x**i*y**j for i in range(3) for j in range(4))

# Entries are coefficients in p (A) or q (B), low-degree first.
A=[[[0],[-1],[1]], [[0,-1],[-1,1],[1]], [[0,-1,1],[-1,1],[1]]]
B=[[[0],[0],[-1],[1]], [[0],[0,-1],[-1,1],[1]],
   [[0,0,-1],[0,-1,1],[-1,1],[1]], [[0,0,-1,1],[0,-1,1],[-1,1],[1]]]
WP=[[0,-1,1],[-1,1],[1]]
WQ=[[0,0,-1,1],[0,-1,1],[-1,1],[1]]
PAIRS=[(a,b) for a in range(3) for b in range(4) if (a,b)!=(2,3)]
STAR={(0,0),(2,0),(1,1),(0,2),(2,2),(1,3)}
STAR_MASK=sum(1<<j for j,ab in enumerate(PAIRS) if ab in STAR)
COEFFICIENTS=[]
for a,b in product(range(3),range(4)):
    row=[]
    for c,d in PAIRS:
        u=shift3(mul(WP[a],A[a][c]),3)
        v=shift3(mul(WQ[b],B[b][d]),4)
        row.append([u[i]*v[j] for i in range(3) for j in range(4)])
    COEFFICIENTS.append(row)

def weighted_rows(mask):
    return [[sum(row[j][k] for j in range(11) if mask>>j&1) for k in range(12)] for row in COEFFICIENTS]
def upper_coeffs(mask):return [sum(abs(row[k]) for row in weighted_rows(mask)) for k in range(12)]
starrows=weighted_rows(STAR_MASK)
assert all(all(c>=0 for c in row) or all(c<=0 for c in row) for row in starrows)
EC=upper_coeffs(STAR_MASK)
assert EC==[1384,1684,678,92,1192,1456,588,80,266,326,132,18]

def star_formula(p,q):
    return ((5*p*p-8*p+4)*(q-1)*(3*q*q-2*q+1)
            +(p-1)*(2*p-1)*(q**3-2*q*q+2*q-2)
            +(p*p-2*p+2)*(q-1)*(q*q+1)+(p-1)*q**3)

def direct(mask,p,q):
    energy=0
    for a,b in product(range(3),range(4)):
        lam=sum(ev1(A[a][c],p)*ev1(B[b][d],q) for j,(c,d) in enumerate(PAIRS) if mask>>j&1)
        energy+=ev1(WP[a],p)*ev1(WQ[b],q)*abs(lam)
    return energy

rows=[];minima=[10**100]*12
started=time.monotonic()
for mask in range(2048):
    bound=upper_coeffs(mask)
    gap=[e-b for e,b in zip(EC,bound)]
    assert all(c>=0 for c in gap),(mask,gap)
    if mask!=STAR_MASK:
        assert gap[0]>=96,(mask,gap)
        minima=[min(a,b) for a,b in zip(minima,gap)]
    else:assert gap==[0]*12
    rows.append([mask]+gap)

# Independent formula evaluations, including boundary equal bases (algebraically
# allowed), different primes, and very imbalanced bases. This is a diagnostic;
# the all-parameter proof uses polynomial identity and the complete certificate.
numeric_pairs=[(3,3),(3,5),(5,3),(7,11),(101,3),(3,1009),(10007,1009)]
for p,q in numeric_pairs:
    assert ev2(EC,p-3,q-3)==star_formula(p,q)==direct(STAR_MASK,p,q)
    for mask in range(2048):
        ws=weighted_rows(mask)
        val=sum(abs(ev2(row,p-3,q-3)) for row in ws)
        assert val==direct(mask,p,q),(p,q,mask,val)
        assert val<=ev2(upper_coeffs(mask),p-3,q-3)
        if mask!=STAR_MASK:assert val<direct(STAR_MASK,p,q)

with (BASE/'circulant-coefficient-gaps.csv').open('w') as f:
    writer=csv.writer(f); writer.writerow(['mask']+[f'gap_x{i}_y{j}' for i in range(3) for j in range(4)]);writer.writerows(rows)
cert={'statement':'all x,y>=0; D* uniquely maximizes the weighted Ramanujan energy',
      'pairs':PAIRS,'star_mask':STAR_MASK,'weighted_basis_coefficients':COEFFICIENTS,
      'star_weighted_rows':starrows,'star_energy_coefficients':EC,
      'masks_checked':2048,'min_gap_excluding_star':minima,
      'numeric_pairs':numeric_pairs,'diagnostic_comparisons':2048*len(numeric_pairs),
      'runtime_seconds':time.monotonic()-started}
(BASE/'circulant-certificate.json').write_text(json.dumps(cert,indent=2))
print(json.dumps({k:v for k,v in cert.items() if k not in ('weighted_basis_coefficients','star_weighted_rows')},indent=2))
for name in ['circulant_certificate.py','circulant-certificate.json','circulant-coefficient-gaps.csv']:
    data=(BASE/name).read_bytes();print(name,len(data),hashlib.sha256(data).hexdigest())
