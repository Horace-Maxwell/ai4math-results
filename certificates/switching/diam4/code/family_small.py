# Stars T(0^k0) and T(1, 0^k0) (k0 >= 2): explicit switchings and exact resultant checks (one parameter k0).
import sympy
t, k0 = sympy.symbols('t k0')
# T(1, 0^k0): centre c, k0 bare leaves (signs: one -1 => E = k0 - 2), middle v sigma = +1, far leaf lambda = L.
sec = t**2 - (k0 + 2) * t + k0          # k0/t + 1/(t-1) = 1
for L in (1, -1):
    E, S = k0 - 2, 1
    P = 1 + L / (t - 1); Q = E / t + S / (t - 1)
    num = sympy.numer(sympy.together(P**2 - t * Q**2))
    res = sympy.factor(sympy.resultant(sympy.Poly(sympy.expand(num), t), sympy.Poly(sec, t)))
    roots = [r for r in sympy.Poly(res, k0).all_roots() if r.is_integer and r >= 2] if sympy.Poly(res, k0).degree() > 0 else []
    print(f"T(1,0^k0), s_c=+1, E=k0-2, S=1, L={L}: Res = {res}; integer roots k0>=2: {roots}")
# Star T(0^k0): secular t = k0; G(theta) = 1 + E/theta, fails iff E^2 = k0.
print('star: E = k0-2 fails iff (k0-2)^2 = k0 iff k0 in', sympy.solve((k0 - 2)**2 - k0, k0), '-> use E = 0 (two flips) for k0 = 4')
