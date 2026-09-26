"""Spot check of the hypotheses (S_a), (F_a), (C_a) of Proposition 'reduction' exactly as written in note.tex,
from the definitions (cells h_mu from the definition), at sample parameter points and on grids of (mu, m, y)."""
from fractions import Fraction as F
import itertools, sys
from cheap_check import T, mv
def h(P, mu, A, B): return P*abs(A-B) + mu*abs(B+P*A) - (P-mu)*abs(B) - P*(1+mu)*abs(A)
def grid(lo, hi, n=4): return [lo + (hi-lo)*F(i, n) for i in range(n+1)]
def run(a, p, q, Pmin):
    x = q; P = x-1
    M = T(a, p); sa = [(-1)**i for i in range(a+1)]
    al = mv(M, sa); d = sum(abs(v) for v in al); de = al[a]
    om = [sum(abs(v) for v in row) for row in M]
    vecs = list(itertools.product([1, -1], repeat=a+1))
    Mc = {c: mv(M, c) for c in vecs}
    Dl = {c: d - sum(abs(v) for v in Mc[c]) for c in vecs}
    def psi(mu, c, zeta):
        B = mv(M, zeta)
        return P*(1+mu)*Dl[c] - sum(h(P, mu, Mc[c][i], B[i]) for i in range(a+1))
    mu0 = (P-1)/x; mu1 = (P*P+1)/(x*x); mui = P/(x+1)
    eta = lambda y, n: y if n == 0 else (P - eta(y, n-1))/x
    bad = 0; n = 0
    # (S_a)
    for c in vecs:
        if list(c) in (sa, [-v for v in sa]): continue
        n += 1
        if not Pmin*Dl[c] > sum(max(0, om[i]-Pmin*abs(Mc[c][i])) for i in range(a+1)): bad += 1; print('S fail', c)
    # (F_a)
    if a % 2 == 0:
        fam = [[(F(1), m, (P-m)/x) for m in grid(mu0, mui)], [(mu, F(1), (P-mu)/x) for mu in grid(mu0, mui)],
               [(mu, m, mu) for mu in grid(mui, mu1) for m in grid(mu0, mui)], [(mu, m, m) for mu in grid(mu0, mui) for m in grid(mui, mu1)]]
    else:
        fam = [[(F(1), F(1), mu0)], [(F(1), m, (P-m)/x) for m in grid(mui, mu1)], [(mu, F(1), (P-mu)/x) for mu in grid(mui, mu1)],
               [(mu, m, mui) for mu in grid(mu0, mui) for m in grid(mu0, mui)] + [(mu, m, mui) for mu in grid(mui, mu1) for m in grid(mui, mu1)]]
    for fa in fam:
        for (mu, m, r) in fa:
            for c in vecs:
                if list(c) == [-v for v in sa]: continue
                n += 1
                if not psi(mu, c, [m*v for v in sa]) > 2*x*de*r: bad += 1; print('F fail', c, mu, m, r)
    # (C_a)
    anti = tuple(-((-1)**a)*v for v in sa)
    gp = tuple(((-1)**a)*v for v in sa[:-1]) + (((-1)**a)*sa[-1]-2,)
    D1 = F(3*x-4, 1)/x; D2 = (5*x*x-8*x+4)/(x*x)
    cheap = 0
    for g in vecs:
        if g[a] != -1 or g in (anti, gp): continue
        if Dl[g] > 2*de: continue
        cheap += 1
        gam = 2*de - Dl[g]
        for k in range(5):
            Ik = grid(mu0, mui) if (k - a) % 2 == 0 else grid(mui, mu1) + [F(1)]
            muk1 = eta(F(1), k)   # mu_{k-1}
            st = [(-1)**k * muk1 * v for v in g]
            for y in Ik:
                chain = sum(P*(1+eta(y, nn))*Dl[g] for nn in range(1, k+1))
                for c in vecs:
                    if c == tuple((-1)**(k+1)*v for v in g): continue
                    n += 1
                    if not chain + psi(y, c, st) > x*eta(y, k+1)*gam: bad += 1; print('C1 fail', g, k, y, c)
        ys = grid(mu0, mui) if a % 2 == 0 else grid(mui, mu1)
        for y in ys:
            n += 1
            if not sum(P*(1+eta(y, nn))*Dl[g] for nn in range(5)) > x*eta(y, 5)*gam: bad += 1; print('C2 fail', g, y)
        n += 1
        if a % 2 == 0:
            if not Dl[g]*(D1/mu1 + 2) > 2*de: bad += 1; print('C3 fail', g)
        else:
            if not (Dl[g]*D1/mu0 > 2*de and Dl[g]*(D2/mui + 2) > 2*de): bad += 1; print('C3 fail', g)
    return n, bad, cheap
for a in (3, 4):
    for (p, q, Pmin) in [(5, 3, 2), (7, 3, 2), (5, 7, 2), (11, 13, 2), (F(11, 2), F(7, 2), 2), (101, 3, 2), (5, 101, 2),
                         (3, 5, 4), (3, 7, 4), (3, 11, 4), (3, F(41, 4), 4), (3, 101, 4)]:
        n, bad, cheap = run(a, F(p), F(q), Pmin)
        print(f'a={a} p={p} q={q}: {n} checks, {bad} failures, {cheap} cheap columns', flush=True)
