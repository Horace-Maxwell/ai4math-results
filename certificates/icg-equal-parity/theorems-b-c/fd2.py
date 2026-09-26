"""Case c_b = B = (1,1,-1): need sum_{j<b} s_j + kappa >= 4 P rho (beyond rho*Delta(B)).
B-chain: c_j = (-1)^j B for J' < j < b (each costs chat_j * Delta(B), cells 0).  First deviation at J' (state (-1)^{J'+1} mu_{b-2-J'} B).
Report min over deviations of [chain cost + s_{J'}] / (4 P rho).  Also J' = -1 (full chain): chain cost / (4 P rho)."""
import sys
from fractions import Fraction as Fr
from core import T, mus, dfun, delta_last
def hfun(Q, mu, A, B):
    return Q * abs(A - B) + mu * abs(B + Q * A) - (Q - mu) * abs(B) - Q * (1 + mu) * abs(A)
Bt = (1, 1, -1)
def run(p, q, b):
    p = Fr(p); q = Fr(q); Q = q - 1; P = p - 1
    M = T(2, p); mu = mus(b + 2, q)
    Dp = dfun(2, p)
    rho = mu[b - 1]; need = 4 * P * rho
    Fp = lambda c: sum(abs(sum(M[i][k] * c[k] for k in range(3))) for i in range(3))
    chat = lambda j: Q * (1 + mu[j - 1]) / q
    worst = None
    chain = Fr(0)
    for Jp in range(b - 1, -2, -1):
        if Jp == -1:
            r = chain / need
            if worst is None or r < worst[0]: worst = (r, 'full chain', Jp)
            break
        eps = (-1) ** (Jp + 1); m = mu[b - 2 - Jp]
        zeta = [eps * m * t for t in Bt]
        Bv = [sum(M[i][k] * zeta[k] for k in range(3)) for i in range(3)]
        for c in [(s0, s1, s2) for s0 in (1, -1) for s1 in (1, -1) for s2 in (1, -1)]:
            if list(c) == [-eps * t for t in Bt]: continue      # chain continuation
            Av = [sum(M[i][k] * c[k] for k in range(3)) for i in range(3)]
            s = chat(Jp) * (Dp - Fp(c)) - sum(hfun(Q, mu[Jp - 1], Av[i], Bv[i]) for i in range(3)) / q
            r = (chain + s) / need
            if worst is None or r < worst[0]: worst = (r, c, Jp)
        chain += chat(Jp) * (Dp - Fp(Bt))
    return worst
if __name__ == "__main__":
    for (p, q) in [(3, 5), (3, 7), (3, 11), (3, 13), (3, 101), (3, 1009), (5, 3), (7, 3), (5, 7), (101, 3)]:
        res = [(b,) + run(p, q, b) for b in [2, 4, 6, 8, 10, 12, 20, 30]]
        w = min(res, key=lambda t: t[1])
        print(f"p={p} q={q}: min ratio (chain+dev)/(4P rho) = {float(w[1]):.4f} at b={w[0]}, dev={w[2]}, J'={w[3]}   " +
              ' '.join(f"b{t[0]}:{float(t[1]):.3f}" for t in res))
