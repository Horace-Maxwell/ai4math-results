"""Exact symbolic verification of Lemma FD1 (7 deviation types, regimes R0, R1, R2a, R2b) and Lemma FD2
(case c_b = B: (i) P>=4: all 8 choices of c_{b-1}; (ii) P=2: B-chain with k=1,2 steps + deviation, k>=3, full chain).
Method: the quantity E (surplus minus need) is concave in each free parameter (mu, m) separately (piecewise linear with
min / -max pieces), so its minimum over the parameter box is attained at a vertex; min(X,Y) is split into both branches,
-c*max(0,Z) into both branches.  Each vertex value is a rational function of (P,Q); positivity is certified on
{P = 4+s, Q = 2+t} and on {P = 2, Q = 4+t} (s,t >= 0) by: denominator = product of manifestly positive factors, numerator
polynomial with all coefficients >= 0 and positive constant term."""
import sympy as sp
import itertools, sys

P, Q, s, t = sp.symbols('P Q s t', nonnegative=True)
mu, m = sp.symbols('mu m', nonnegative=True)
q = Q + 1; p = P + 1
mu0 = (Q - 1) / (Q + 1); mu1 = (Q**2 + 1) / (Q + 1)**2; L = Q / (Q + 2)
D = 5*P**2 + 2*P + 1; dl = P**2 + 1

class Mn:   # symbolic min / max branches
    pass

def branches(expr_fn):
    """expr_fn(choose) where choose(list_of_alternatives) picks one; enumerate all combinations of choices.
    For min(X,Y): alternatives [X, Y] (need all positive). For -c*max(0,Z): alternatives [0, -c Z]."""
    out = []
    def rec(choices):
        idx = [0]
        seq = []
        def choose(alts):
            k = idx[0]; idx[0] += 1
            if k < len(choices): return alts[choices[k]]
            seq.append(len(alts)); return alts[0]
        val = expr_fn(choose)
        if seq:     # more choices to enumerate
            for c in range(seq[0]):
                rec(choices + [c])
        else:
            out.append(val)
    rec([])
    return out

def s_FD1(dev, MU, M, choose):
    chat = Q * (1 + MU) / q; muJ = (Q - MU) / q
    if dev == 'Asame': return 2 * muJ * M * D
    if dev == 'Bsame':
        return 2*(P-1)**2*chat + 2*muJ*dl*M + (4*P/q) * choose([(Q - MU)*P*M, Q - MU*P*M])
    if dev == 'Bopp':
        return 2*(P-1)**2*chat + 4*muJ*p*P*M + choose([0, -(4*MU*P/q)*(P*M - Q)])
    if dev == 'Csame':
        return 2*dl*chat - (4*MU/q)*p*P*M + 4*muJ*P**2*M + (2/q)*choose([(Q - MU)*dl*M, Q*(P**2-1) - MU*dl*M])
    if dev == 'Copp': return 2*dl*chat - (4*MU/q)*p*P*M
    if dev == 'Esame': return 4*P**2*chat - (4*MU/q)*(p*P + P**2)*M + 2*muJ*dl*M
    if dev == 'Eopp': return 4*P**2*chat - (4*MU/q)*(p*P + P**2)*M

def s_chain(dev, MU, M, choose):
    chat = Q * (1 + MU) / q; muJ = (Q - MU) / q
    if dev == 'Asame': return 4*muJ*P*M + (2/q)*choose([(Q - MU)*(p**2-2)*M, Q*dl - MU*(p**2-2)*M])
    if dev == 'Aopp': return 4*muJ*p*P*M
    if dev == 'Bsame': return 2*(P-1)**2*chat + 2*muJ*M*(3*p**2 - 4)
    if dev == 'Bopp': return 2*(P-1)**2*chat       # chain continuation (used for FD2(i))
    if dev == 'Csame':
        return 2*dl*chat - (4*MU/q)*p*P*M + 4*muJ*P*M + (2/q)*choose([(Q - MU)*(p**2-2)*M, Q*(P**2-1) - MU*(p**2-2)*M])
    if dev == 'Copp': return 2*dl*chat - (4*MU/q)*p*P*M
    if dev == 'Esame': return 4*P**2*chat - (4*MU/q)*(p*P + P)*M + 2*muJ*(p**2-2)*M
    if dev == 'Eopp': return 4*P**2*chat - (4*MU/q)*(p*P + P)*M

def certify(expr, region):
    """region 'big': P=4+s, Q=2+t ; 'p3': P=2, Q=4+t.  Returns (ok, info)."""
    if region == 'big': e = expr.subs({P: 4 + s, Q: 2 + t}, simultaneous=True)
    else: e = expr.subs({P: 2, Q: 4 + t}, simultaneous=True)
    e = sp.together(sp.expand(e))
    num, den = sp.fraction(e)
    num = sp.expand(num)
    # denominator: factor and check each factor is a polynomial with nonnegative coefficients (positive on region)
    dfac = sp.factor_list(den)
    okden = dfac[0] > 0 or True
    sign = sp.sign(dfac[0])
    for f, k in dfac[1]:
        pf = sp.Poly(f, s, t)
        cs = pf.coeffs()
        if all(c >= 0 for c in cs): continue
        if all(c <= 0 for c in cs):
            sign *= (-1) ** k; continue
        return False, ('den factor', f)
    if sign < 0: num = -num
    pn = sp.Poly(num, s, t)
    coeffs = dict(zip(pn.monoms(), pn.coeffs()))
    const = coeffs.get((0, 0), 0)
    neg = {k: v for k, v in coeffs.items() if v < 0}
    return (const > 0 and not neg), (const, neg)

def check(name, expr_fn, regions=('big', 'p3')):
    allok = True
    for reg in regions:
        for val in branches(expr_fn):
            ok, info = certify(sp.simplify(val), reg)
            if not ok:
                allok = False
                print(f"   FAIL {name} region={reg}: const={info[0]} neg={info[1] if isinstance(info[1], dict) else info}")
    return allok

results = []
def run_FD1():
    for dev in ['Asame', 'Bsame', 'Bopp', 'Csame', 'Copp', 'Esame', 'Eopp']:
        # R0: J=0, mu=1, m in {mu0, L}, rho = (Q-m)/q
        for Mv, lab in [(mu0, 'mu0'), (L, 'L')]:
            ok = check(f"FD1 {dev} R0 m={lab}", lambda ch, Mv=Mv: s_FD1(dev, 1, Mv, ch) - 2*dl*(Q - Mv)/q)
            results.append((f"FD1 {dev} R0 m={lab}", ok))
        # R1: J=b-1, m=1, mu in {mu0, L}, rho = (Q-mu)/q
        for MUv, lab in [(mu0, 'mu0'), (L, 'L')]:
            ok = check(f"FD1 {dev} R1 mu={lab}", lambda ch, MUv=MUv: s_FD1(dev, MUv, 1, ch) - 2*dl*(Q - MUv)/q)
            results.append((f"FD1 {dev} R1 mu={lab}", ok))
        # R2a: mu in [L, mu1] (odd), m in [mu0, L] (even), rho <= mu
        for (MUv, a), (Mv, b_) in itertools.product([(L, 'L'), (mu1, 'mu1')], [(mu0, 'mu0'), (L, 'L')]):
            ok = check(f"FD1 {dev} R2a mu={a} m={b_}", lambda ch, MUv=MUv, Mv=Mv: s_FD1(dev, MUv, Mv, ch) - 2*dl*MUv)
            results.append((f"FD1 {dev} R2a mu={a} m={b_}", ok))
        # R2b: mu in [mu0, L] (even), m in [L, mu1] (odd), rho <= m
        for (MUv, a), (Mv, b_) in itertools.product([(mu0, 'mu0'), (L, 'L')], [(L, 'L'), (mu1, 'mu1')]):
            ok = check(f"FD1 {dev} R2b mu={a} m={b_}", lambda ch, MUv=MUv, Mv=Mv: s_FD1(dev, MUv, Mv, ch) - 2*dl*Mv)
            results.append((f"FD1 {dev} R2b mu={a} m={b_}", ok))

def run_FD2():
    # (i) all P (incl. P=2 where possible): J = b-1, state B (m=1), mu = mu_{b-2} in [mu0, L], rho = (Q-mu)/q; need 4 P rho
    for dev in ['Asame', 'Aopp', 'Bsame', 'Csame', 'Copp', 'Esame', 'Eopp']:
        for MUv, lab in [(mu0, 'mu0'), (L, 'L')]:
            ok = check(f"FD2 J=b-1 {dev} mu={lab}", lambda ch, MUv=MUv: s_chain(dev, MUv, 1, ch) - 4*P*(Q - MUv)/q)
            results.append((f"FD2 J=b-1 {dev} mu={lab}", ok))
    # chain continuation -B at J=b-1 pays alone when P>=4:
    for MUv, lab in [(mu0, 'mu0'), (L, 'L')]:
        ok = check(f"FD2(i) -B at b-1 (P>=4) mu={lab}", lambda ch, MUv=MUv: s_chain('Bopp', MUv, 1, ch) - 4*P*(Q - MUv)/q, regions=('big',))
        results.append((f"FD2(i) -B at b-1 (P>=4) mu={lab}", ok))
    # (ii) P = 2: B-chain.  k = number of chain steps before the deviation at J' = b-1-k.
    # k=1: J' = b-2; m = mu_0; mu = mu_{b-3}: odd in [L, mu1] (b>=4) or mu = 1 (b=2); x = mu_{b-2} = (Q-mu)/q; rho=(Q-x)/q
    for dev in ['Asame', 'Aopp', 'Bsame', 'Csame', 'Copp', 'Esame', 'Eopp']:
        for MUv, lab in [(L, 'L'), (mu1, 'mu1'), (sp.Integer(1), 'one')]:
            def f(ch, MUv=MUv):
                x = (Q - MUv) / q; rho = (Q - x) / q
                chain = 2 * (P - 1)**2 * Q * (1 + x) / q
                return chain + s_chain(dev, MUv, mu0, ch) - 4*P*rho
            ok = check(f"FD2(ii) k=1 {dev} mu={lab}", f, regions=('p3',))
            results.append((f"FD2(ii) k=1 {dev} mu={lab}", ok))
    # k=2: J' = b-3 >= 1 (b>=4); m = mu_1; mu = mu_{b-4} even in [mu0, L]; y = mu_{b-3} = (Q-mu)/q; x = mu_{b-2} = (Q-y)/q
    for dev in ['Asame', 'Aopp', 'Bsame', 'Csame', 'Copp', 'Esame', 'Eopp']:
        for MUv, lab in [(mu0, 'mu0'), (L, 'L')]:
            def f(ch, MUv=MUv):
                y = (Q - MUv) / q; x = (Q - y) / q; rho = (Q - x) / q
                chain = 2 * (P - 1)**2 * Q * (2 + x + y) / q
                return chain + s_chain(dev, MUv, mu1, ch) - 4*P*rho
            ok = check(f"FD2(ii) k=2 {dev} mu={lab}", f, regions=('p3',))
            results.append((f"FD2(ii) k=2 {dev} mu={lab}", ok))
    # k>=3 (chain alone): chain >= 2(P-1)^2 Q [(1+x) + (1+L) + (1+mu0)]/q with x = mu_{b-2} in [mu0, L], rho = (Q-x)/q
    for Xv, lab in [(mu0, 'mu0'), (L, 'L')]:
        ok = check(f"FD2(ii) k>=3 chain alone x={lab}",
                   lambda ch, Xv=Xv: 2*(P-1)**2*Q*((1 + Xv) + (1 + L) + (1 + mu0))/q - 4*P*(Q - Xv)/q, regions=('p3',))
        results.append((f"FD2(ii) k>=3 chain alone x={lab}", ok))

if __name__ == "__main__":
    run_FD1(); run_FD2()
    nfail = sum(1 for r in results if not r[1])
    for r in results:
        print(("OK   " if r[1] else "FAIL ") + r[0])
    print(f"TOTAL {len(results)} vertex checks, failures: {nfail}")
