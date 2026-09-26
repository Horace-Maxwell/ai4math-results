"""Referee-3: symbolic check (SymPy, independent of the integer code) of the facts (12)-(13) of Section 10 of Paper 1 for
a = 2..8.  They are proved by hand for all a in the paper; Lemma 22 and Lemma 24 (the equality step) use nothing else.
  (12) u_i = p^{a-1-i} R, alpha_i = (-1)^{a-i} p^{a-1} R (1 + mu^(p)_{i-1}), row i of M has one negative entry -p^{a-1} R and
       nonnegative entries summing to p^{a-1} R (so omega_i = 2 p^{a-1} R), for i < a; u_a = 1, row a sums to p^a.
  (13) |alpha_i| - 2u_i = 0 for i = 0 and > 0 for 0 < i < a;  delta_a - 3 > 0;  P delta_a - p^a > 0;  P|alpha_i| - omega_i > 0,
       on R1 (p = 5 + s, P = 2 + t) and R2 (p = 3, P = 4 + t), by the coefficient test.
Also: delta_a = (p^a (p-1) + 2(-1)^a)/(p+1) and d_a = (2a+1)p^a + 4 sum_{j<a} (-1)^{a-j}(j+1)p^j (closed forms of Remark 9), and
Delta(g_+) = 2 delta_a, via the sign pattern (M g_+)_i = (-1)^i (|alpha_i| - 2(-1)^i u_i) with nonnegative brackets.
"""
import sympy as sp

p, s, t = sp.symbols('p s t', positive=True)


def T(k):
    M = sp.zeros(k + 1, k + 1)
    for i in range(k + 1):
        for j in range(k + 1):
            if i < k and j < k:
                v = 0 if i + j <= k - 2 else (-p ** (k - 1) * (p - 1) if i + j == k - 1 else p ** (2 * k - i - j - 2) * (p - 1) ** 2)
            elif i == k and j == k:
                v = 1
            else:
                v = p ** (k - (i if i < k else j) - 1) * (p - 1)
            M[i, j] = sp.expand(v)
    return M


def cert_pos(expr, region):
    """coefficient test for expr > 0 on the region (expr polynomial in p and t)."""
    e = sp.expand(expr.subs(p, 5 + s) if region == 'R1' else expr.subs(p, 3))
    pl = sp.Poly(e, s, t)
    co = dict(zip(pl.monoms(), pl.coeffs()))
    return all(c >= 0 for c in co.values()) and co.get((0, 0), 0) > 0


ok_all = True
for a in range(2, 9):
    M = T(a)
    R = p - 1
    sa = sp.Matrix([(-1) ** i for i in range(a + 1)])
    alpha = (M * sa).applyfunc(sp.expand)
    u = M[:, a]
    mup = {-1: sp.Integer(1)}
    for j in range(a):
        mup[j] = sp.cancel((p - 1 - mup[j - 1]) / p)
    ok = True
    absal = [sp.expand((-1) ** (a - i) * alpha[i]) for i in range(a + 1)]
    for i in range(a):
        ok &= sp.expand(u[i] - p ** (a - 1 - i) * R) == 0
        ok &= sp.cancel(alpha[i] - (-1) ** (a - i) * p ** (a - 1) * R * (1 + mup[i - 1])) == 0
        negs = [M[i, j] for j in range(a + 1) if M[i, j] != 0 and M[i, j].subs(p, 5) < 0]
        poss = [M[i, j] for j in range(a + 1) if M[i, j] != 0 and M[i, j].subs(p, 5) > 0]
        ok &= len(negs) == 1 and sp.expand(negs[0] + p ** (a - 1) * R) == 0
        ok &= sp.expand(sum(poss) - p ** (a - 1) * R) == 0
    ok &= u[a] == 1 and sp.expand(sum(M[a, j] for j in range(a + 1)) - p ** a) == 0
    delta = alpha[a]
    ok &= sp.cancel(delta - (p ** a * (p - 1) + 2 * (-1) ** a) / (p + 1)) == 0
    d_closed = (2 * a + 1) * p ** a + 4 * sum((-1) ** (a - j) * (j + 1) * p ** j for j in range(a))
    ok &= sp.expand(sum(absal) - d_closed) == 0           # sign pattern (-1)^{a-i} of alpha_i is certified below
    omega = [2 * p ** (a - 1) * R] * a + [p ** a]
    for region, Pv in (('R1', 2 + t), ('R2', 4 + t)):
        for i in range(a + 1):
            ok &= cert_pos(absal[i], region)                                  # sign of alpha_i is (-1)^{a-i}
        ok &= sp.expand(absal[0] - 2 * u[0]) == 0
        for i in range(1, a):
            ok &= cert_pos(absal[i] - 2 * u[i], region)
        ok &= cert_pos(delta - 3, region)
        ok &= cert_pos(Pv * delta - p ** a, region)
        for i in range(a + 1):
            ok &= cert_pos(Pv * absal[i] - omega[i], region)
        # Delta(g_+) = 2 delta_a: (M g_+)_i = (-1)^a alpha_i - 2 u_i = (-1)^i (|alpha_i| - 2(-1)^i u_i), brackets >= 0
        gp = sp.Matrix([((-1) ** a) * (-1) ** i for i in range(a + 1)])
        gp[a] -= 2
        Mg = (M * gp).applyfunc(sp.expand)
        l1 = 0
        for i in range(a + 1):
            br = sp.expand(absal[i] - 2 * (-1) ** i * u[i])
            ok &= sp.expand(Mg[i] - (-1) ** i * br) == 0
            ok &= (br == 0) or cert_pos(br, region)
            l1 += br
        ok &= sp.expand(sum(absal) - l1 - 2 * delta) == 0
    print(f'a={a}: (12), (13), closed forms of d_a and delta_a, Delta(g_+) = 2 delta_a on R1 and R2: {"OK" if ok else "FAILED"}',
          flush=True)
    ok_all &= bool(ok)
print('ALL OK' if ok_all else 'SOME CHECK FAILED')
