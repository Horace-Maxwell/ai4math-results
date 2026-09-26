"""Lemma S: for every column c in {+-1}^3, every state zeta in [-1,1]^3 and every mu in [0,1]:
  s(c,zeta) = chat*Delta(c) - (1/q) sum_i h_mu((T2 c)_i, (T2 zeta)_i) >= 0,  and > 0 unless c = +-s_2;
plus the explicit lower bounds used in the proof. Random exact test on both parameter regions."""
import random
from fractions import Fraction as Fr
from core import T, dfun
def hfun(Q, mu, A, B):
    return Q * abs(A - B) + mu * abs(B + Q * A) - (Q - mu) * abs(B) - Q * (1 + mu) * abs(A)
random.seed(7)
cnt = 0
for trial in range(3000):
    if trial % 2: P = Fr(random.randint(4, 40)) + Fr(random.randint(0, 9), 10); Q = Fr(2) + Fr(random.randint(0, 300), 10)
    else: P = Fr(2); Q = Fr(4) + Fr(random.randint(0, 300), 10)
    p = P + 1; q = Q + 1
    M = T(2, p); Dp = dfun(2, p)
    mu = Fr(random.randint(0, 1000), 1000)
    chat = Q * (1 + mu) / q
    zeta = [Fr(random.randint(-1000, 1000), 1000) for _ in range(3)]
    if trial % 5 == 0:  # push to cube corners/edges
        zeta = [Fr(random.choice([-1, 1])) if random.random() < 0.7 else z for z in zeta]
    Bv = [sum(M[i][k] * zeta[k] for k in range(3)) for i in range(3)]
    for c in [(a, b, d) for a in (1, -1) for b in (1, -1) for d in (1, -1)]:
        Av = [sum(M[i][k] * c[k] for k in range(3)) for i in range(3)]
        F = sum(abs(x) for x in Av)
        s = chat * (Dp - F) - sum(hfun(Q, mu, Av[i], Bv[i]) for i in range(3)) / q
        e = c[0]; t = tuple(e * x for x in c)
        assert s >= 0, (P, Q, mu, zeta, c, s)
        if t == (1, 1, -1):
            lb = (2 / q) * (Q * (1 + mu) * (P - 1) ** 2 - 2 * mu * P * max(0, p - Q)); assert s >= lb > 0
        if t == (1, -1, -1):
            lb = (4 / q) * (P * P - P + 2); assert s >= lb
        if t == (1, 1, 1):
            lb = (8 * P / q) * (P - mu); assert s >= lb
        cnt += 1
print(f"Lemma S and its explicit lower bounds hold in {cnt} random exact checks")
