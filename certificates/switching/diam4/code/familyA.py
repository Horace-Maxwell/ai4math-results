# Family A(k1, k0) = T(1^k1, 0^k0), k0 >= 2, k1 >= 2: centre c with k0 pendant leaves and k1 pendant P_2's.
# Switching: s_c = +1; bare leaves: one -1, others +1 (E = k0 - 2); middle vertices sigma = +1 (S = k1);
# far leaves: one -1, others +1 (L = k1 - 2).
# Secular eigenvalues: theta^2 = t with t^2 - (1+k0+k1) t + k0 = 0.
# G(theta) = [1 + L/(t-1)] + theta [E/t + S/(t-1)] = P(t) + theta Q(t).
# Failure on a secular pair  <=>  P(t)^2 = t Q(t)^2 ; failure on an even orbit needs P = Q = 0.
import sympy
t, k0, k1 = sympy.symbols('t k0 k1')
E, S, L = k0 - 2, k1, k1 - 2
P = 1 + L / (t - 1)
Q = E / t + S / (t - 1)
fail = sympy.together(P**2 - t * Q**2)
num = sympy.factor(sympy.numer(fail))
sec = t**2 - (1 + k0 + k1) * t + k0
print('failure numerator:', num)
res = sympy.factor(sympy.resultant(sympy.Poly(sympy.expand(num), t), sympy.Poly(sec, t)))
print('Res_t(failure numerator, secular):', res)
# simultaneous P = Q = 0 at a secular root:
resP = sympy.factor(sympy.resultant(sympy.Poly(sympy.expand(sympy.numer(sympy.together(P))), t), sympy.Poly(sec, t)))
resQ = sympy.factor(sympy.resultant(sympy.Poly(sympy.expand(sympy.numer(sympy.together(Q))), t), sympy.Poly(sec, t)))
print('Res(P-numerator, secular):', resP)
print('Res(Q-numerator, secular):', resQ)
# brute-force check of integer zeros of the resultant in a box
zeros = [(a, b) for a in range(2, 400) for b in range(2, 400) if res.subs({k0: a, k1: b}) == 0]
print('integer zeros (k0,k1) in [2,400)^2:', zeros[:20], len(zeros))

# Sign certificate: substitute k0 = u + 2, k1 = v + 2 (u, v >= 0) and inspect the coefficients.
u, v = sympy.symbols('u v')
Rs = sympy.Poly(sympy.expand(res.subs({k0: u + 2, k1: v + 2})), u, v)
coeffs = Rs.terms()
print('number of monomials:', len(coeffs))
print('positive coefficients:', [(m, c) for m, c in coeffs if c > 0])
print('constant term:', Rs.coeff_monomial(1))
print('max coefficient:', max(c for m, c in coeffs), ' min:', min(c for m, c in coeffs))
