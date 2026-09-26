"""Automated per-a version of the Theorem B argument (column path over q, F-side T_a(p)), exact symbolic.

For fixed a (and b of the same parity, arbitrary), regions: 'big' P = 4+s, Q = 2+t (p >= 5, q >= 3) and 'p3' P = 2, Q = 4+t.
Checks (each a finite list of bivariate polynomial positivity certificates, b-uniform):
  (S)   Lemma S_a (one-step bound, crude form, all states in the cube, strict for non-alternating columns);
  (FD1) first deviation from the anti-checkerboard, all 2^{a+1}-1 deviations, parity-dependent regimes;
  (CH)  for every 'cheap' last column g (g_a = -1, Delta(g) < 2 delta_a): g-chain analysis (deviations after k <= K chain steps,
        chain-alone bound for k > K, full chain);
  (EQ)  the only non-cheap last column with Delta = 2 delta_a is the truncated-checkerboard column, and the first alternating
        step after it is forced.
Surplus of column c at state eps*m*v (v = M g_state), potential mu:
  s = Q(1+mu)/q * Delta(c) + (1/q) sum_i T_i,  with A = M c, B = eps*m*v:
  A_i = 0: T_i = -2 mu m |v_i|;  A_i B_i > 0: T_i = 2 min((Q-mu) m|v_i|, Q|A_i| - mu m|v_i|);  A_i B_i < 0: T_i = -2 mu (m|v_i| - Q|A_i|)^+.
"""
import itertools, sys, time
import sympy as sp

P, Q, s, t, mu, m, y = sp.symbols('P Q s t mu m y', real=True)
p = P + 1; q = Q + 1
mu0 = (Q - 1) / q; mu1 = (Q**2 + 1) / q**2; L = Q / (q + 1)

def Tsym(k):
    x = p
    Mx = [[sp.Integer(0)] * (k + 1) for _ in range(k + 1)]
    for i in range(k + 1):
        for j in range(k + 1):
            if i < k and j < k:
                if i + j <= k - 2: v = 0
                elif i + j == k - 1: v = -x**(k - 1) * (x - 1)
                else: v = x**(2 * k - i - j - 2) * (x - 1)**2
            elif i == k and j == k: v = 1
            else:
                tt = i if i < k else j
                v = x**(k - tt - 1) * (x - 1)
            Mx[i][j] = sp.expand(v)
    return Mx

def sub(expr, region):
    if region == 'big': return expr.subs({P: 4 + s, Q: 2 + t}, simultaneous=True)
    return expr.subs({P: 2, Q: 4 + t}, simultaneous=True)

_cache = {}
def sign_on(expr, region):
    """+1 / -1 / 0 if the sign of expr is constant on the region (certified by coefficient signs), else None."""
    key = (sp.srepr(expr), region)
    if key in _cache: return _cache[key]
    e = sp.together(sp.expand(sub(expr, region)))
    num, den = sp.fraction(e)
    num = sp.expand(num); den = sp.expand(den)
    if num == 0: _cache[key] = 0; return 0
    def psign(poly_expr):
        pl = sp.Poly(poly_expr, s, t)
        cs = dict(zip(pl.monoms(), pl.coeffs()))
        c0 = cs.get((0, 0), 0)
        if all(v >= 0 for v in cs.values()) and c0 > 0: return 1
        if all(v <= 0 for v in cs.values()) and c0 < 0: return -1
        return None
    sd = None
    fl = sp.factor_list(den)
    sd = sp.sign(fl[0])
    for f, k in fl[1]:
        ps = psign(f)
        if ps is None: _cache[key] = None; return None
        sd *= ps**k
    sn = psign(num)
    r = None if sn is None else int(sn * sd)
    _cache[key] = r
    return r

def positive(expr, region):
    return sign_on(expr, region) == 1

class Prover:
    def __init__(self, a, K=4, verbose=False):
        self.a = a; self.K = K; self.verbose = verbose
        self.M = Tsym(a)
        self.sa = [(-1)**i for i in range(a + 1)]
        self.vecs = list(itertools.product([1, -1], repeat=a + 1))
        self.Mv = {c: [sp.expand(sum(self.M[i][k] * c[k] for k in range(a + 1))) for i in range(a + 1)] for c in self.vecs}
        self.alpha = self.Mv[tuple(self.sa)]
        self.nchecks = 0; self.fails = []

    # absolute value of a P-polynomial on a region (sign must be determined)
    def absr(self, e, region):
        sg = sign_on(e, region)
        if sg is None: raise RuntimeError(f"undetermined sign of {e} on {region}")
        return sg * e

    def F(self, c, region): return sum(self.absr(x, region) for x in self.Mv[c])
    def D(self, region): return self.F(tuple(self.sa), region)
    def delta(self): return self.alpha[self.a]      # (T_a s_a)_a > 0

    def surplus_terms(self, c, v, MU, M_, region):
        """returns (base, list of alternatives lists) for s = base + sum_i choice_i ; each alternatives list must all be checked."""
        A = self.Mv[c]
        base = Q * (1 + MU) / q * (self.D(region) - self.F(c, region))
        alts = []
        for i in range(self.a + 1):
            sa_ = sign_on(A[i], region)
            sv = sign_on(v[i], region)
            if sa_ is None or sv is None: raise RuntimeError("undetermined sign")
            absv = sv * v[i]
            if sa_ == 0:
                base += (-2 * MU * M_ * absv) / q
            elif sv == 0:
                continue
            elif sa_ * sv > 0:
                absA = sa_ * A[i]
                X = 2 * (Q - MU) * M_ * absv; Yv = 2 * (Q * absA - MU * M_ * absv)
                alts.append([X / q, Yv / q])
            else:
                absA = sa_ * A[i]
                Z = M_ * absv - Q * absA
                alts.append([sp.Integer(0), -2 * MU * Z / q])
        return base, alts

    def certify_all(self, name, base, alts, region):
        ok = True
        for combo in itertools.product(*alts) if alts else [()]:
            e = base + sum(combo)
            self.nchecks += 1
            if not positive(e, region):
                ok = False
                self.fails.append((name, region))
                if self.verbose: print("   FAIL", name, region)
                break
        return ok

    # ---------------- Lemma S_a (crude, at mu = 1 and Q = Q_min; monotone in Q, affine in mu) ----------------
    def lemmaS(self):
        for region, Qmin in (('big', 2), ('p3', 4)):
            mx = [sum(self.absr(self.M[i][k], region) for k in range(self.a + 1)) for i in range(self.a + 1)]
            for c in self.vecs:
                A = self.Mv[c]
                Dc = self.D(region) - self.F(c, region)
                terms = []
                for i in range(self.a + 1):
                    absA = self.absr(A[i], region)
                    x = (mx[i] - Q * absA).subs(Q, Qmin)
                    sg = sign_on(x, region)
                    if sg in (0, -1): continue
                    terms.append([sp.Integer(0), x] if sg is None else [x])
                lhs = (2 * Q * Dc).subs(Q, Qmin)
                is_alt = list(c) in (self.sa, [-v for v in self.sa])
                for combo in itertools.product(*terms) if terms else [()]:
                    e = lhs - 2 * sum(combo)
                    self.nchecks += 1
                    sg = sign_on(e, region)
                    if is_alt:
                        if sg not in (0, 1) or (sp.simplify(sub(e, region)) != 0 and sg != 1): self.fails.append((f"S {c}", region))
                    elif sg != 1:
                        self.fails.append((f"S {c}", region))

    # ---------------- FD1_a ----------------
    def regimes_FD1(self):
        """list of (label, MU-values, M-values, rho-expression builder) ; MU, M given as lists of vertex values."""
        if self.a % 2 == 0:
            return [('R0', [sp.Integer(1)], [mu0, L], lambda MU, M_: (Q - M_) / q),
                    ('R1', [mu0, L], [sp.Integer(1)], lambda MU, M_: (Q - MU) / q),
                    ('R2a', [L, mu1], [mu0, L], lambda MU, M_: MU),
                    ('R2b', [mu0, L], [L, mu1], lambda MU, M_: M_)]
        return [('B1', [sp.Integer(1)], [sp.Integer(1)], lambda MU, M_: mu0),
                ('R0', [sp.Integer(1)], [L, mu1], lambda MU, M_: (Q - M_) / q),
                ('R1', [L, mu1], [sp.Integer(1)], lambda MU, M_: (Q - MU) / q),
                ('R2odd', [L, mu1], [L, mu1], lambda MU, M_: L),
                ('R2even', [mu0, L], [mu0, L], lambda MU, M_: L)]

    def FD1(self):
        neg_sa = tuple(-v for v in self.sa)
        for region in ('big', 'p3'):
            dl = self.delta()
            for tvec in self.vecs:
                if tvec == neg_sa: continue
                for lab, MUs, Ms, rho_f in self.regimes_FD1():
                    for MU, M_ in itertools.product(MUs, Ms):
                        base, alts = self.surplus_terms(tvec, self.alpha, MU, M_, region)
                        base = base - 2 * dl * rho_f(MU, M_)
                        self.certify_all(f"FD1 t={tvec} {lab}", base, alts, region)

    # ---------------- chains for cheap last columns ----------------
    def mu_iter(self, x, n):
        for _ in range(n): x = (Q - x) / q
        return x

    def y_values(self, idx_parity_even, allow_one):
        vals = [mu0, L] if idx_parity_even else [L, mu1]
        if allow_one: vals = vals + [sp.Integer(1)]
        return vals

    def chains(self):
        a = self.a
        bpar = a % 2                          # b has the parity of a
        anti_last = tuple(-((-1)**bpar) * v for v in self.sa)
        trunc_last = tuple([((-1)**bpar) * v for v in self.sa][:-1] + [((-1)**bpar) * self.sa[-1] - 2])
        self.cheap = {}
        for region in ('big', 'p3'):
            dl = self.delta(); Dr = self.D(region)
            for g in self.vecs:
                if g[a] != -1 or g == anti_last: continue
                Dg = Dr - self.F(g, region)
                sg = sign_on(2 * dl - Dg, region)
                if g == tuple(trunc_last) or sg in (0, -1):
                    if g == tuple(trunc_last):
                        if sp.simplify(sub(2 * dl - Dg, region)) != 0: self.fails.append((f"EQ Delta(trunc) != 2delta", region))
                    elif sg == 0: self.fails.append((f"EQ other column with Delta = 2 delta {g}", region))
                    continue
                self.cheap.setdefault(region, []).append(g)
                extra_coef = 2 * dl - Dg          # extra need = extra_coef * rho
                v = self.Mv[g]
                # k = number of chain steps before the deviation (k = 0: deviation right after c_b)
                for k in range(0, self.K + 1):
                    # y = mu_{b-2-k}; index parity: b even -> parity of k; b odd -> parity of k+1 ; special y = 1 iff b = k+1
                    idx_even = ((k % 2 == 0) if bpar == 0 else (k % 2 == 1))
                    allow_one = ((k + 1) % 2 == bpar)
                    if k == 0 and bpar == 0: allow_one = False     # b = 1 impossible for even b
                    M_ = sp.Integer(1) if k == 0 else self.mu_iter(sp.Integer(1), k)   # mu_{k-1}
                    for Y0 in self.y_values(idx_even, allow_one):
                        rho = self.mu_iter(Y0, k + 1)
                        chain = sum(Q * (1 + self.mu_iter(Y0, k + 1 - i)) / q for i in range(1, k + 1)) * Dg
                        eps = 1 if k % 2 == 0 else -1
                        cont = tuple(-eps * x for x in g)
                        for c in self.vecs:
                            if c == cont: continue
                            tvec = tuple(eps * x for x in c)      # relative to the state sign
                            base, alts = self.surplus_terms(tvec, v, Y0, M_, region)
                            base = base + chain - extra_coef * rho
                            self.certify_all(f"CH g={g} k={k} t={tvec}", base, alts, region)
                # chain alone for k >= K+1: y = mu_{b-2-K} (index >= 0), parity: b even -> parity of K ; b odd -> K+1
                idx_even = ((self.K % 2 == 0) if bpar == 0 else (self.K % 2 == 1))
                for Y0 in self.y_values(idx_even, False):
                    chain = sum(Q * (1 + self.mu_iter(Y0, self.K + 1 - i)) / q for i in range(1, self.K + 2)) * Dg
                    rho = self.mu_iter(Y0, self.K + 1)
                    self.nchecks += 1
                    if not positive(chain - extra_coef * rho, region): self.fails.append((f"CH g={g} chain-alone K={self.K}", region))
                # full chain: Delta(g) * Dhat_b > 2 delta rho_b  (kappa >= 0 dropped), b-uniform bounds
                d1 = (3 * q - 4) / q; d2 = (5 * q**2 - 8 * q + 4) / q**2
                if bpar == 0:
                    ratio = d1 / mu1 + 2            # Dhat_b/rho_b >= Dhat_1/mu_1 + 2 (b even >= 2)
                    conds = [Dg * ratio - 2 * dl]
                else:
                    conds = [Dg * (d1 / mu0) - 2 * dl,            # b = 1: Dhat_1/rho_1 exactly d1/mu0
                             Dg * (d2 / L + 2) - 2 * dl]          # b >= 3: Dhat_b/rho_b >= Dhat_2/L + 2
                for e in conds:
                    self.nchecks += 1
                    if not positive(e, region): self.fails.append((f"CH g={g} full chain", region))

    def eq_forcing(self):
        """state = truncated last column g; the alternating choice with the WRONG sign has a strictly negative cell."""
        a = self.a; bpar = a % 2
        g = tuple([((-1)**bpar) * v for v in self.sa][:-1] + [((-1)**bpar) * self.sa[-1] - 2])
        for region in ('big', 'p3'):
            v = self.Mv[g]
            wrong = tuple(((-1)**bpar) * x for x in self.sa)      # Y+ uses (-1)^{b-1} s_a at column b-1
            A = self.Mv[wrong]
            found = any(sign_on(A[i], region) not in (None, 0) and sign_on(v[i], region) not in (None, 0)
                        and sign_on(A[i], region) * sign_on(v[i], region) > 0 for i in range(a + 1))
            self.nchecks += 1
            if not found: self.fails.append(("EQ forcing", region))
            right = tuple(-x for x in wrong)
            # right choice must have all cells zero: opposite signs (or v_i = 0) and |v_i| <= Q_min |A_i|
            A = self.Mv[right]
            for i in range(a + 1):
                sv = sign_on(v[i], region); sa_ = sign_on(A[i], region)
                if sv == 0: continue
                if sa_ is None or sv is None or sa_ * sv > 0: self.fails.append(("EQ right-choice sign", region)); continue
                Qmin = 2 if region == 'big' else 4
                self.nchecks += 1
                if sign_on((Qmin * sa_ * A[i] - sv * v[i]), region) not in (0, 1): self.fails.append(("EQ right-choice bound", region))

    def run(self):
        t0 = time.time()
        self.lemmaS(); n1 = self.nchecks
        self.FD1(); n2 = self.nchecks
        self.chains(); n3 = self.nchecks
        self.eq_forcing()
        print(f"a={self.a}: checks S={n1}, FD1={n2-n1}, chains={n3-n2}, EQ={self.nchecks-n3}; cheap last columns: "
              f"{ {r: len(v) for r, v in self.cheap.items()} }; failures: {len(self.fails)}  ({time.time()-t0:.0f}s)")
        for f in self.fails[:20]: print("   FAIL:", f)
        sys.stdout.flush()
        return not self.fails

if __name__ == "__main__":
    for a in [int(x) for x in sys.argv[1:]] or [2]:
        Prover(a).run()
