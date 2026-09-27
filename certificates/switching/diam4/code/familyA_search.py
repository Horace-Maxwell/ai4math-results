# Search, for family A(k1,k0) = T(1^k1, 0^k0) (k0 >= 2, k1 >= 2), for a switching (s_c, E, S, L) whose failure
# resultant Res_t(P^2 - t Q^2, secular) has constant sign on k0 = u+2, k1 = v+2 (u, v >= 0): all coefficients of
# the same sign in (u, v) => no failure for ANY k0, k1 >= 2.
import sympy, itertools
t, k0, k1, u, v = sympy.symbols('t k0 k1 u v')
sec = t**2 - (1 + k0 + k1) * t + k0
cands = []
for sc in (1, -1):
    for E in (k0 - 2, -(k0 - 2)):
        for (S, L, desc) in [(k1, k1 - 2, 'sigma=1, one leaf -1'), (k1, -(k1 - 2), 'sigma=1, one leaf +1'),
                             (k1 - 2, k1, 'one sigma -1, leaves +1'), (k1 - 2, -k1, 'one sigma -1, leaves -1'),
                             (-(k1 - 2), k1, 'one sigma +1 (rest -1), leaves +1'), (-k1, k1 - 2, 'sigma=-1, one leaf -1')]:
            P = sc + L / (t - 1); Q = E / t + S / (t - 1)
            num = sympy.numer(sympy.together(P**2 - t * Q**2))
            res = sympy.resultant(sympy.Poly(sympy.expand(num), t), sympy.Poly(sec, t))
            Rs = sympy.Poly(sympy.expand(res.subs({k0: u + 2, k1: v + 2})), u, v)
            cs = [c for m, c in Rs.terms()]
            sign = 'POS' if all(c >= 0 for c in cs) and Rs.coeff_monomial(1) > 0 else ('NEG' if all(c <= 0 for c in cs) and Rs.coeff_monomial(1) < 0 else 'mixed')
            resQ = sympy.factor(sympy.resultant(sympy.Poly(sympy.expand(sympy.numer(sympy.together(Q))), t), sympy.Poly(sec, t)))
            cands.append((sign, sc, str(E), desc))
            print(sign, 's_c=', sc, 'E=', E, desc, ' Res(Q,sec)=', resQ, flush=True)
