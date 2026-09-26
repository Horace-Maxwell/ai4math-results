from sympy import isprime, bernoulli, Rational
import itertools
def K(b):
    r=1
    for q in range(2,b+1):
        if isprime(q) and (b-1)%(q-1)==0: r*=q
    return r
ok=[b for b in range(3,200,2) if (2*b)%K(b)==0]
print('odd b<200 with K_b | 2b:',ok)
print('denominator check:',all(Rational(bernoulli(b-1)).q==K(b) for b in range(3,200,2)))
print('odd b<200 with 3|b:',[b for b in range(3,200,2) if b%3==0])
# min 2n for odd b>=5 from moreover: sum_{v=2}^{(b+1)/2} v^2
for b in [5,7,9,11,13,15,17,27]:
    s=sum(v*v for v in range(2,(b+1)//2+1)); print(b,'sum',s,'n>=',-(-s//2))
# r_max
def sumsmallest(r):
    s=0;c=0;v=2
    while c<r:
        for t in range(4):
            if c==r: break
            s+=v*v;c+=1
        v+=1
    return s
for N in [41,42,49]:
    r=0
    while sumsmallest(r+1)<=2*N: r+=1
    print('N',N,'rmax',r, 'sumsmallest(r)',sumsmallest(r),'next',sumsmallest(r+1))
print('sumsmallest(10)',sumsmallest(10),'sumsmallest(14)',sumsmallest(14))
# minimal S2 over admissible B+ multisets of size s (rho simple >=3, others mult<=2, values 2..9)
best={}
for cp in itertools.product(range(3),repeat=8):
    vals=list(range(2,10)); 
    rho=max([v for v,c in zip(vals,cp) if c>0],default=0)
    if rho<3 or cp[rho-2]!=1: continue
    s=sum(cp); S2=sum(c*v*v for v,c in zip(vals,cp))
    if s not in best or S2<best[s][0]: best[s]=(S2,[ (v,c) for v,c in zip(vals,cp) if c])
for s in sorted(best): print('|B+|=',s,'min S2',best[s])
# all B+ with |B+|=5 and S2<=42
for cp in itertools.product(range(3),repeat=8):
    vals=list(range(2,10)); rho=max([v for v,c in zip(vals,cp) if c>0],default=0)
    if rho<3 or cp[rho-2]!=1: continue
    if sum(cp)>=5 and sum(c*v*v for v,c in zip(vals,cp))<=42: print('size>=5,S2<=42:',[(v,c) for v,c in zip(vals,cp) if c])
