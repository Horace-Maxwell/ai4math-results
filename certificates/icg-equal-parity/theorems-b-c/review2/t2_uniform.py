"""Referee-2, test 2.  The uniform surplus formula of PROOF.md sec. 11.

 (A) Derivation check.  For the cell h_mu(A,B) = Q|A-B| + mu|B+QA| - (Q-mu)|B| - Q(1+mu)|A| we derive (case analysis, A >= 0,
     then h(-A,-B) = h(A,B)):  -h = -2 mu |B| if A = 0;  2 min{(Q-mu)|B|, Q|A| - mu|B|} if AB > 0;
     -2 mu (|B| - Q|A|)^+ if AB < 0;  0 if B = 0.  Verified exactly on 200 000 random rational (A, B, Q, mu), Q >= 2, mu in [0,1].
 (B) Referee's own implementation of s = Q(1+mu)Delta(c)/q + (1/q) sum_i T_i at a state eps*m*v (v = M g) against the
     direct cell computation, a = 3, 4, random g, c, eps, m in (0,1], mu in [0,1], P, Q in both regions.
 (C) The AUTHORS' implementation (generic_prover.Prover.surplus_terms, symbolic, region-certified signs) evaluated at the same
     points (min over the listed alternatives) against the direct computation.
"""
import itertools, random, sys, os
from fractions import Fraction as Fr
from r2core import T, matvec, l1, svec, dd, h, surplus_direct
sys.path.insert(0, os.path.abspath('..'))
import sympy as sp

random.seed(7)
out = open('logs/t2_uniform.log', 'w')
def log(*a):
    s = ' '.join(str(x) for x in a); print(s); out.write(s + '\n'); out.flush()

# (A)
def negh_formula(Q, mu, A, B):
    if A == 0:
        return -2 * mu * abs(B)
    if B == 0:
        return Fr(0)
    if A * B > 0:
        return 2 * min((Q - mu) * abs(B), Q * abs(A) - mu * abs(B))
    return -2 * mu * max(Fr(0), abs(B) - Q * abs(A))

for _ in range(200000):
    Q = Fr(2) + Fr(random.randint(0, 300), random.randint(1, 40))
    mu = Fr(random.randint(0, 50), 50)
    A = Fr(random.randint(-60, 60), random.randint(1, 7)) * random.choice([0, 1, 1, 1])
    B = Fr(random.randint(-300, 300), random.randint(1, 7)) * random.choice([0, 1, 1, 1, 1])
    assert -h(Q, mu, A, B) == negh_formula(Q, mu, A, B), (Q, mu, A, B)
log("(A) cell case formula (-h) verified on 200000 random exact points: OK")

# (B)
def s_uniform(M, Da, Q, q, mu, m, eps, g, c):
    v = matvec(M, g)
    tv = [eps * x for x in c]                   # relative to the state sign
    A = matvec(M, tv)
    tot = Q * (1 + mu) * (Da - l1(A))
    for i in range(len(v)):
        if A[i] == 0:
            tot += -2 * mu * m * abs(v[i])
        elif v[i] == 0:
            pass
        elif A[i] * v[i] > 0:
            tot += 2 * min((Q - mu) * m * abs(v[i]), Q * abs(A[i]) - mu * m * abs(v[i]))
        else:
            tot += -2 * mu * max(Fr(0), m * abs(v[i]) - Q * abs(A[i]))
    return tot / q

def rand_point(region):
    if region == 'big':
        P = Fr(4) + Fr(random.randint(0, 200), random.randint(1, 13)); Q = Fr(2) + Fr(random.randint(0, 200), random.randint(1, 13))
    else:
        P = Fr(2); Q = Fr(4) + Fr(random.randint(0, 200), random.randint(1, 13))
    return P, Q

n = 0
for a in (3, 4):
    vecs = list(itertools.product([1, -1], repeat=a + 1))
    for trial in range(6000):
        region = 'big' if trial % 2 == 0 else 'p3'
        P, Q = rand_point(region); p, q = P + 1, Q + 1
        M = T(a, p); Da = dd(a, p)
        g = list(random.choice(vecs)); c = list(random.choice(vecs))
        if trial % 4 == 0: g = svec(a)                                  # FD1 states
        eps = random.choice([1, -1])
        m = Fr(random.randint(1, 60), 60); mu = Fr(random.randint(0, 60), 60)
        zeta = [eps * m * x for x in g]
        sd = surplus_direct(M, Da, Q, q, mu, c, zeta)
        su = s_uniform(M, Da, Q, q, mu, m, eps, g, c)
        assert sd == su, (a, P, Q, g, c, eps, m, mu, sd, su)
        n += 1
log(f"(B) referee's uniform surplus formula == direct cell computation: {n} random exact cases (a = 3, 4, both regions, "
    f"random g incl. g = s_a, eps, m, mu): OK")

# (C) authors' implementation
import generic_prover as GP
PS, QS = GP.P, GP.Q
n = 0
for a in (3, 4):
    pr = GP.Prover(a)
    vecs = pr.vecs
    for trial in range(300 if a == 3 else 150):
        region = 'big' if trial % 2 == 0 else 'p3'
        P, Q = rand_point(region); p, q = P + 1, Q + 1
        M = T(a, p); Da = dd(a, p)
        g = random.choice(vecs); c = random.choice(vecs)
        if trial % 3 == 0: g = tuple(svec(a))
        eps = random.choice([1, -1])
        m = Fr(random.randint(1, 60), 60); mu = Fr(random.randint(0, 60), 60)
        tvec = tuple(eps * x for x in c)
        base, alts = pr.surplus_terms(tvec, pr.Mv[tuple(g)], sp.Rational(mu.numerator, mu.denominator),
                                      sp.Rational(m.numerator, m.denominator), region)
        subs = {PS: sp.Rational(P.numerator, P.denominator), QS: sp.Rational(Q.numerator, Q.denominator)}
        val = sp.Rational(base.subs(subs)) + sum(min(sp.Rational(x.subs(subs)) for x in alt) for alt in alts)
        val = Fr(int(sp.numer(val)), int(sp.denom(val)))
        zeta = [eps * m * x for x in g]
        sd = surplus_direct(M, Da, Q, q, mu, list(c), zeta)
        assert sd == val, (a, P, Q, g, c, eps, m, mu, sd, val)
        n += 1
log(f"(C) authors' surplus_terms (symbolic, region-certified signs; min over alternatives) == direct cell computation: "
    f"{n} random exact cases, a = 3, 4: OK")
