"""Check the polynomial inequalities (I1)-(I7), (I5b) of the new Section 10 in the paper's notation
(R = p - 1, P = q - 1), and the hand-proof identities quoted in the text.  Exact (sympy)."""
import sympy as sp

R, P, s, t = sp.symbols('R P s t')
T = (R**2 + 1) * (P**2 + 1)
I = {
    'I1': (P - 1)**2 * (5*R**2 + 2*R + 1) - T,
    'I2': P*(P + 1)*(R - 1)**2 + (P - 1)**2 * (3*R**2 + 1) - T,
    'I3': (R**2 + 1)*(P - 1) + (P + 1)*(2*P*(R**2 - R + 1) - 3*R**2 - 1),
    'I4': P*(P + 1)*(R - 1)**2 + 2*(P - 1)**2 * R*(R + 1) - T,
    'I5': (P + 1)*P*(2*R**2 - 6*R) + 2*P**2*(P + 1)*(R + 1) - T,
    'I5b': (P + 1)*P*(R - 1)**2 + 2*P**2*(P + 1)*(R + 1) - T,
    'I6': P*(P + 1)**2 * (R**2 + 1) - 2*R*(R + 1)*(P**2 + 1),
    'I7': 2*R*(P*R - 1)*(P + 1) - T,
}
# Lean statements (ICGEqualParityBCol.lean), with Lean P -> R, Lean Q -> P
LP, LQ = R, P
lean = {
    'I1': (LQ - 1)**2 * (5*LP**2 + 2*LP + 1) - (LP**2 + 1)*(LQ**2 + 1),
    'I2': (LP - 1)**2 * LQ*(LQ + 1) + (LQ - 1)**2 * (3*LP**2 + 1) - (LP**2 + 1)*(LQ**2 + 1),
    'I3': 2*(LP**2 + 1)*(LQ - 1) + (LQ + 1)*(2*LQ*(LP - 1)**2 + 2*LQ*(LP**2 + 1) - 6*LP**2 - 2),
    'I4': 2*(LP - 1)**2*LQ*(LQ + 1) + 4*(LQ - 1)**2*LP*(LP + 1) - 2*(LP**2 + 1)*(LQ**2 + 1),
    'I5': (LQ + 1)*(2*LQ*(2*LP**2 - 6*LP)) + 4*LQ**2*(LQ + 1)*(LP + 1) - 2*(LP**2 + 1)*(LQ**2 + 1),
    'I5b': (LQ + 1)*(2*(LP - 1)**2*LQ + 4*LQ**2*(LP + 1)) - 2*(LP**2 + 1)*(LQ**2 + 1),
    'I6': (LP**2 + 1)*LQ*(LQ + 1)**2 - 2*LP*(LP + 1)*(LQ**2 + 1),
    'I7': 4*LP*(LP*LQ - 1)*(LQ + 1) - 2*(LP**2 + 1)*(LQ**2 + 1),
}
ok = True
for k in I:
    ratio = sp.simplify(lean[k] / I[k])
    print(k, 'Lean/paper ratio =', ratio)
    ok &= ratio.is_number and ratio > 0
    for name, sub in [('R=4+s,P=2+t', {R: 4 + s, P: 2 + t}), ('R=2,P=4+t', {R: 2, P: 4 + t})]:
        poly = sp.Poly(sp.expand(I[k].subs(sub)), s, t)
        coeffs = poly.coeffs()
        const = poly.as_expr().subs({s: 0, t: 0})
        good = all(c >= 0 for c in coeffs) and const > 0
        print('   ', name, 'nonneg coeffs & const>0:', good, ' const =', const)
        if not good:
            print('      poly =', poly.as_expr())
        if k != 'I5' or name.startswith('R=4'):
            ok &= good

# hand-proof identities
chk = []
chk.append(sp.expand((5*R**2 + 2*R + 1) - 5*(R**2 + 1) - 2*(R - 2)))
chk.append(sp.expand(5*(P - 1)**2 - (P**2 + 1) - 2*(2*P - 1)*(P - 2)))
chk.append(sp.expand(2*I['I7'] - (P*R*(P*R - 4) + P**2*(R**2 - 2) + (4*R**2*P - 2*R**2 - 4*R - 2))))
chk.append(sp.expand(P*(P + 1)**2 - ((P + 2)*(P**2 + 1) - 2)))
chk.append(sp.expand(I['I5b'] - ((R - 1)**2*(P - 1) + 2*(R*(P**3 - 1) + P**3 + P**2))))
chk.append(sp.expand(I['I4'] - ((R - 1)**2*(P - 1) + 2*R*((P - 1)**2*(R + 1) - P**2 - 1))))
chk.append(sp.expand(I['I2'] - ((R - 1)**2*(P - 1) + (P - 1)**2*(3*R**2 + 1) - 2*R*(P**2 + 1))))
chk.append(sp.expand(18*(R**2 + 1) - 10*R*(R + 1) - (8*R**2 - 10*R + 18)))
print('hand identities all zero:', all(c == 0 for c in chk), chk)
ok &= all(c == 0 for c in chk)
print('ALL OK' if ok else 'FAILURE')
