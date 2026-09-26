"""(a) Lemma 1 (path identity) on random rational vectors; Lemma 2 identity on all sign vectors;
basic JY identities (symmetry, row sums, T s = (-1)^m Delta s, tr Delta = d_m, (1.4))."""
import random, itertools, time
from fractions import Fraction as Fr
from rv_core import *

random.seed(20260925)
t0 = time.time()
fails = []

# 0. Ramanujan-sum sanity: Kluyver vs exponential sum, and T_ram == T_gen for primes
for m in range(1, 60):
    for t in range(0, 70):
        if abs(ramanujan(m, t) - ramanujan_numeric(m, t)) > 1e-6:
            fails.append(('ramanujan', m, t))
print('ramanujan Kluyver vs exp-sum: checked m<60, t<70')
cnt = 0
for x in [2, 3, 5, 7, 11]:
    for m in range(1, 8 if x < 7 else 5):
        if x ** m > 20000:
            continue
        A = T_ram(m, x)
        B = T_gen(m, x)
        if any(A[i][j] != B[i][j] for i in range(m + 1) for j in range(m + 1)):
            fails.append(('T_ram!=T_gen', x, m))
        cnt += 1
print('T_ram == T_gen for primes: %d cases' % cnt)

# 0b. T_gen equals JY's explicit polynomial entries (2.3)-(2.4) for real (rational) x
def T_explicit(k, x):
    t = [[Fr(0)] * (k + 1) for _ in range(k + 1)]
    for i in range(k + 1):
        for j in range(k + 1):
            if i < k and j < k:
                if i + j <= k - 2: t[i][j] = Fr(0)
                elif i + j == k - 1: t[i][j] = -x ** (k - 1) * (x - 1)
                else: t[i][j] = x ** (2 * k - i - j - 2) * (x - 1) ** 2
            elif i == k and j == k: t[i][j] = Fr(1)
            else:
                e = min(i, j)
                t[i][j] = x ** (k - e - 1) * (x - 1)
    return t
ne = 0
for x in [Fr(3), Fr(4), Fr(5, 2), Fr(7, 3), Fr(13, 4), Fr(101, 20), Fr(17, 3), Fr(29, 7), Fr(9), Fr(12)] + [Fr(v, 3) for v in range(20, 34)]:
    for k in range(1, 13):
        if T_explicit(k, x) != T_gen(k, x):
            fails.append(('T_gen != (2.3)-(2.4)', x, k))
        ne += 1
print('T_gen == explicit (2.3)-(2.4): %d (x,k) pairs, k=1..12, 24 x-values > max degree+1 = 13, so polynomial identity' % ne)

# 1. structural identities for many x (integers and rationals)
xs = [Fr(3), Fr(4), Fr(5), Fr(7), Fr(11), Fr(5, 2), Fr(7, 3), Fr(21, 4), Fr(13, 4), Fr(101, 20)]
for x in xs:
    for m in range(1, 11):
        T = T_gen(m, x)
        # symmetric
        if any(T[i][j] != T[j][i] for i in range(m + 1) for j in range(m + 1)):
            fails.append(('sym', x, m))
        # row sums = x^m e_m
        rs = [sum(r) for r in T]
        if rs != [0] * m + [x ** m]:
            fails.append(('rowsum', x, m))
        s = svec(m)
        D = delta_diag(m, x)
        Ts = matvec(T, s)
        if Ts != [(-1) ** m * D[i] * s[i] for i in range(m + 1)]:
            fails.append(('Ts', x, m))
        if sum(D) != d_formula(m, x):
            fails.append(('trace', x, m))
        if x > 2 and not all(d > 0 for d in D):
            fails.append(('Dpos', x, m))
        if x > 2 and l1(Ts) != d_formula(m, x):
            fails.append(('l1Ts', x, m))
        mu, c = mu_c(m, x)
        if x > 2 and x ** m * (sum(c.values()) + mu[m - 1]) != d_formula(m, x):
            fails.append(('d=x^m(sum c+mu)', x, m))
        if x > 2 and not all((x - 2) / x <= mu[k] <= 1 for k in mu):
            fails.append(('mu range', x, m))
print('structural identities: x in %s, m=1..10' % [str(v) for v in xs])

# 2. Lemma 1 on random rational vectors (also per-coordinate and signed forms)
n_l1 = 0
for x in xs + [Fr(2), Fr(3, 2)]:
    for m in range(1, 10):
        T = T_gen(m, x)
        for trial in range(40):
            w = [Fr(random.randint(-50, 50), random.randint(1, 12)) for _ in range(m + 1)]
            Tw = matvec(T, w)
            z = zpath(w, x)
            # convex-combination closed form
            for k in range(-1, m):
                cf = sum((Fr(1) if m - i == 0 else x ** (m - i - 1) * (x - 1)) * w[i]
                         for i in range(k + 1, m + 1)) / x ** (m - k - 1)
                if cf != z[k]:
                    fails.append(('zclosed', x, m, k))
            if Tw[m] != x ** m * z[-1]:
                fails.append(('row m', x, m))
            for k in range(m):
                u = m - 1 - k
                if Tw[u] != x ** (m - 1) * (x - 1) * (z[k] - w[k]):
                    fails.append(('signed row', x, m, k))
                if abs(Tw[u]) != x ** m * abs(z[k - 1] - z[k]):
                    fails.append(('abs row', x, m, k))
            rhs = x ** m * (abs(z[-1]) + sum(abs(z[k - 1] - z[k]) for k in range(m)))
            if l1(Tw) != rhs:
                fails.append(('lemma1', x, m))
            n_l1 += 1
print('Lemma 1: %d random rational vectors, x in xs+{2,3/2}, m=1..9' % n_l1)

# 3. Lemma 2 identity for every sign vector (x>2), plus sign/size claims
n_l2 = 0
for x in [Fr(3), Fr(4), Fr(5), Fr(7), Fr(5, 2), Fr(21, 10), Fr(13, 4)]:
    for m in range(1, 12 if x in (3, 5) else 9):
        T = T_gen(m, x)
        mu, c = mu_c(m, x)
        dm = d_formula(m, x)
        for y in itertools.product([1, -1], repeat=m + 1):
            z = zpath(list(map(Fr, y)), x)
            for k in range(-1, m):
                if (z[k] > 0) != (y[k + 1] > 0) or abs(z[k]) < (x - 2) / x or abs(z[k]) > 1:
                    fails.append(('zsign', x, m, y, k))
            if abs(z[m - 1]) != 1:
                fails.append(('zlast', x, m, y))
            NA = [k for k in range(m) if y[k] == y[k + 1]]
            lhs = l1(matvec(T, list(y))) / x ** m
            rhs = sum(c.values()) + mu[m - 1] - sum(2 * mu[k] * abs(z[k]) for k in NA)
            if lhs != rhs:
                fails.append(('lemma2 id', x, m, y))
            # f_k case values
            for k in range(m):
                fk = abs(z[k - 1] - z[k]) + mu[k - 1] * abs(z[k - 1]) - mu[k] * abs(z[k])
                want = c[k] - (2 * mu[k] * abs(z[k]) if k in NA else 0)
                if fk != want:
                    fails.append(('fk', x, m, y, k))
            v = l1(matvec(T, list(y)))
            if list(y) in (svec(m), [-e for e in svec(m)]):
                if v != dm:
                    fails.append(('eq case', x, m, y))
            elif not v < dm:
                fails.append(('strict', x, m, y))
            n_l2 += 1
print('Lemma 2: %d (x,m,y) triples, all sign vectors' % n_l2)

print('FAILURES:', len(fails), fails[:10])
print('time %.1fs' % (time.time() - t0))
