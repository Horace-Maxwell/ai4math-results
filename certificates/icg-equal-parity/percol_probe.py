"""Probe the Part-A case structure for general shapes in the column-path (q-path) accounting, exact.
Columns c_k in {+-1}^{a+1} are the inputs, F(c) = ||T_a(p) c||_1 (F-side), path over the q side.
Per column k < b:  s_k = chat_k (D_a - F(c_k)) - (1/q) sum_u h_q(w^(u)_k, z_k(w^(u)))   (w^(u) = row u of T_a(p) Y)
Last column: s_b = rho_b (D_a - F(c_b)).  Corner: kappa = 2 (z_{-1}(w^(a)))^-.   Identity: target-G = (sum s) - 2 delta_a rho_b + kappa... (scaled by q^b).
Questions: (1) is s_k >= 0 for every column k < b?  (2) if column k < b is non-alternating, is s_k >= need = 2 delta_a rho_b / q^b?
(3) what fails?
"""
import itertools, sys
from fractions import Fraction as Fr
from core import T, dfun, delta_last, path, Gval, target

def mus(m, x):
    mu = {-1: Fr(1)}
    for k in range(m): mu[k] = (x - 1 - mu[k - 1]) / x
    return mu

def hfun(P, mu, A, B):
    return P * abs(A - B) + mu * abs(B + P * A) - (P - mu) * abs(B) - P * (1 + mu) * abs(A)

def probe(a, b, p, q, limit=None):
    p = Fr(p); q = Fr(q); Pq = q - 1
    M = T(a, p); muq = mus(b, q)
    chat = {k: Pq * (1 + muq[k - 1]) / q for k in range(b)}; chat[b] = muq[b - 1]
    Da = dfun(a, p); need = 2 * delta_last(a, p) * delta_last(b, q) / q ** b
    s_alt = [(-1) ** i for i in range(a + 1)]
    cells = [(i, j) for i in range(a + 1) for j in range(b + 1)]
    free = [c for c in cells if c != (a, b)]
    neg_sk = 0; E_fail = 0; E_total = 0; examples = []
    minratio = None
    for bits in itertools.product([1, -1], repeat=len(free)):
        Y = {c: s for c, s in zip(free, bits)}; Y[(a, b)] = -1
        cols = [[Fr(Y[(i, k)]) for i in range(a + 1)] for k in range(b + 1)]
        Mc = [[sum(M[u][i] * cols[k][i] for i in range(a + 1)) for u in range(a + 1)] for k in range(b + 1)]
        F = [sum(abs(t) for t in Mc[k]) for k in range(b + 1)]
        s = []
        for k in range(b):
            hsum = Fr(0)
            for u in range(a + 1):
                w = [Mc[kk][u] for kk in range(b + 1)]
                z = path(w, q)
                hsum += hfun(Pq, muq[k - 1], w[k], z[k])
            s.append(chat[k] * (Da - F[k]) - hsum / q)
        for k in range(b):
            if s[k] < 0:
                neg_sk += 1
                if len(examples) < 3: examples.append(('neg', k, [[Y[(i, j)] for j in range(b + 1)] for i in range(a + 1)], float(s[k])))
            isalt = cols[k] == [Fr(t) for t in s_alt] or cols[k] == [Fr(-t) for t in s_alt]
            if not isalt:
                E_total += 1
                r = s[k] / need
                if minratio is None or r < minratio[0]:
                    minratio = (r, k, [[Y[(i, j)] for j in range(b + 1)] for i in range(a + 1)])
                if s[k] < need:
                    E_fail += 1
    return neg_sk, E_fail, E_total, minratio, examples

if __name__ == "__main__":
    for (a, b, p, q) in [(2, 2, 5, 3), (2, 2, 40, 3), (2, 2, 3, 5), (2, 2, 7, 5), (3, 3, 5, 3), (2, 4, 5, 3), (4, 2, 5, 3), (4, 2, 3, 5), (1, 3, 5, 3), (3, 1, 5, 3)]:
        neg, Ef, Et, mr, ex = probe(a, b, p, q)
        print(f"(a,b,p,q)=({a},{b},{p},{q}): #neg s_k={neg}  E-columns (k<b) with s_k < need: {Ef}/{Et}  "
              f"min s_k/need over E-columns = {float(mr[0]):.4f} at k={mr[1]} Y={mr[2]}")
        for e in ex: print("    ", e)
        sys.stdout.flush()
