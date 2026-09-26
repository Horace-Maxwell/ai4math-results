"""Fast port of generic_prover.py (same mathematics, same check list), with exact integer arithmetic:
every quantity is a rational function  num(s,t) / (q^K (q+1)^L)  where num has integer coefficients, q = Q+1, and
  region 'big': P = 4+s, Q = 2+t   (q = 3+t, q+1 = 4+t);    region 'p3': P = 2, Q = 4+t   (q = 5+t, q+1 = 6+t).
The denominators are positive on the region, so the sign of a quantity is certified by the coefficient test on num
(all coefficients >= 0 with positive constant term => positive).  Uses the uniform surplus formula of PROOF.md §11.
Usage: python3 generic_fast2.py a [K]"""
import itertools, sys, time

# ---------- integer polynomials in (s,t): dict {(i,j): int} ----------
def padd(a, b, c=1):
    r = dict(a)
    for k, v in b.items():
        w = r.get(k, 0) + c * v
        if w: r[k] = w
        else: r.pop(k, None)
    return r
def pmul(a, b):
    r = {}
    for (i, j), v in a.items():
        for (k, l), w in b.items():
            key = (i + k, j + l); x = r.get(key, 0) + v * w
            if x: r[key] = x
            else: r.pop(key, None)
    return r
def pscal(a, c): return {k: v * c for k, v in a.items()} if c else {}
_powcache = {}
def ppow(base, n, key):
    k = (key, n)
    if k not in _powcache:
        r = {(0, 0): 1}
        for _ in range(n): r = pmul(r, base)
        _powcache[k] = r
    return _powcache[k]

class Region:
    def __init__(self, name):
        self.name = name
        if name == 'big': self.P = {(0, 0): 4, (1, 0): 1}; self.Q = {(0, 0): 2, (0, 1): 1}; self.Q0 = 2
        else: self.P = {(0, 0): 2}; self.Q = {(0, 0): 4, (0, 1): 1}; self.Q0 = 4
        self.q = padd(self.Q, {(0, 0): 1}); self.q1 = padd(self.Q, {(0, 0): 2})

class RF:
    __slots__ = ('R', 'n', 'K', 'L')
    def __init__(self, R, n, K=0, L=0): self.R = R; self.n = n; self.K = K; self.L = L
    def lift(self, K, L):
        n = self.n
        if K > self.K: n = pmul(n, ppow(self.R.q, K - self.K, (self.R.name, 'q')))
        if L > self.L: n = pmul(n, ppow(self.R.q1, L - self.L, (self.R.name, 'q1')))
        return n
    def __add__(self, o):
        if not isinstance(o, RF): o = const(self.R, o)
        K = max(self.K, o.K); L = max(self.L, o.L)
        return RF(self.R, padd(self.lift(K, L), o.lift(K, L)), K, L)
    __radd__ = __add__
    def __neg__(self): return RF(self.R, pscal(self.n, -1), self.K, self.L)
    def __sub__(self, o): return self + (-o if isinstance(o, RF) else const(self.R, -o))
    def __rsub__(self, o): return (-self) + o
    def __mul__(self, o):
        if not isinstance(o, RF): return RF(self.R, pscal(self.n, o), self.K, self.L)
        return RF(self.R, pmul(self.n, o.n), self.K + o.K, self.L + o.L)
    __rmul__ = __mul__
    def div_q(self, k=1): return RF(self.R, self.n, self.K + k, self.L)
    def div_q1(self, k=1): return RF(self.R, self.n, self.K, self.L + k)
    def sign(self):
        if not self.n: return 0
        c0 = self.n.get((0, 0), 0); vals = self.n.values()
        if c0 > 0 and all(v >= 0 for v in vals): return 1
        if c0 < 0 and all(v <= 0 for v in vals): return -1
        return None
def const(R, c): return RF(R, {(0, 0): c} if c else {})
def poly(R, p): return RF(R, dict(p))

def T_region(R, k):
    P = poly(R, R.P); p = P + 1
    M = [[None] * (k + 1) for _ in range(k + 1)]
    def pw(x, e):
        r = const(R, 1)
        for _ in range(e): r = r * x
        return r
    for i in range(k + 1):
        for j in range(k + 1):
            if i < k and j < k:
                if i + j <= k - 2: v = const(R, 0)
                elif i + j == k - 1: v = -(pw(p, k - 1) * (p - 1))
                else: v = pw(p, 2 * k - i - j - 2) * (p - 1) * (p - 1)
            elif i == k and j == k: v = const(R, 1)
            else:
                tt = i if i < k else j
                v = pw(p, k - tt - 1) * (p - 1)
            M[i][j] = v
    return M

class FastProver:
    def __init__(self, a, K=4):
        self.a = a; self.K = K
        self.sa = tuple((-1) ** i for i in range(a + 1))
        self.vecs = list(itertools.product([1, -1], repeat=a + 1))
        self.fails = []; self.counts = {}
    def cnt(self, k): self.counts[k] = self.counts.get(k, 0) + 1
    def setup(self, rname):
        R = self.R = Region(rname); a = self.a
        self.M = T_region(R, a)
        self.Mv = {c: [sum((self.M[i][k] * c[k] for k in range(a + 1)), const(R, 0)) for i in range(a + 1)] for c in self.vecs}
        self.sg = {}
        for c in self.vecs:
            ss = [x.sign() for x in self.Mv[c]]
            if any(z is None for z in ss): raise RuntimeError(f"undetermined sign of (Mc)_i for {c} on {rname}")
            self.sg[c] = ss
        self.absMv = {c: [self.Mv[c][i] * self.sg[c][i] for i in range(a + 1)] for c in self.vecs}
        self.alpha = self.Mv[self.sa]; self.delta = self.alpha[a]
        self.D = sum(self.absMv[self.sa], const(R, 0))
        self.Delta = {c: self.D - sum(self.absMv[c], const(R, 0)) for c in self.vecs}
        Q = self.Qf = poly(R, R.Q)
        self.mu0 = (Q - 1).div_q(); self.mu1 = (Q * Q + 1).div_q(2); self.L = Q.div_q1(); self.one = const(R, 1)
    def f(self, y, n=1):
        for _ in range(n): y = (self.Qf - y).div_q()
        return y
    def terms(self, c, vec, vsg, MU, M_):
        """uniform surplus formula: returns (base, alternatives) for q-free form s = base + sum(choice)."""
        R = self.R; Q = self.Qf
        base = (Q * (MU + 1) * self.Delta[c]).div_q()
        alts = []
        for i in range(self.a + 1):
            sA = self.sg[c][i]; sv = vsg[i]
            absv = vec[i] * sv
            if sA == 0:
                base = base - (MU * M_ * absv * 2).div_q()
            elif sv == 0:
                continue
            elif sA * sv > 0:
                absA = self.absMv[c][i]
                alts.append([((Q - MU) * M_ * absv * 2).div_q(), ((Q * absA - MU * M_ * absv) * 2).div_q()])
            else:
                absA = self.absMv[c][i]
                alts.append([const(R, 0), -((MU * (M_ * absv - Q * absA)) * 2).div_q()])
        return base, alts
    def certify(self, name, base, alts):
        for combo in (itertools.product(*alts) if alts else [()]):
            e = base
            for x in combo: e = e + x
            self.cnt(name.split()[0])
            if e.sign() != 1:
                self.fails.append((name, self.R.name)); return False
        return True
    def lemmaS(self):
        R = self.R; a = self.a; Qm = R.Q0
        for i in range(a + 1):
            for k in range(a + 1):
                if self.M[i][k].sign() is None: raise RuntimeError("undetermined sign of a T_a entry")
        mx = [sum((self.M[i][k] * (self.M[i][k].sign() or 1) for k in range(a + 1)), const(R, 0)) for i in range(a + 1)]
        for c in self.vecs:
            is_alt = c in (self.sa, tuple(-x for x in self.sa))
            terms = []
            for i in range(a + 1):
                x = mx[i] - self.absMv[c][i] * Qm
                s_ = x.sign()
                if s_ in (0, -1): continue
                terms.append([const(R, 0), x] if s_ is None else [x])
            lhs = self.Delta[c] * (2 * Qm)
            for combo in (itertools.product(*terms) if terms else [()]):
                e = lhs
                for x in combo: e = e - x * 2
                self.cnt('S'); s_ = e.sign()
                if is_alt:
                    if s_ not in (0, 1): self.fails.append((f"S {c}", R.name))
                elif s_ != 1: self.fails.append((f"S {c}", R.name))
    def FD1(self):
        a = self.a; one = self.one; mu0, mu1, L = self.mu0, self.mu1, self.L; Q = self.Qf
        if a % 2 == 0:
            regs = [('R0', [one], [mu0, L], lambda MU, M_: (Q - M_).div_q()), ('R1', [mu0, L], [one], lambda MU, M_: (Q - MU).div_q()),
                    ('R2a', [L, mu1], [mu0, L], lambda MU, M_: MU), ('R2b', [mu0, L], [L, mu1], lambda MU, M_: M_)]
        else:
            regs = [('B1', [one], [one], lambda MU, M_: mu0), ('R0', [one], [L, mu1], lambda MU, M_: (Q - M_).div_q()),
                    ('R1', [L, mu1], [one], lambda MU, M_: (Q - MU).div_q()), ('R2odd', [L, mu1], [L, mu1], lambda MU, M_: L),
                    ('R2even', [mu0, L], [mu0, L], lambda MU, M_: L)]
        nsa = tuple(-x for x in self.sa); vsg = self.sg[self.sa]
        for t_ in self.vecs:
            if t_ == nsa: continue
            for lab, MUs, Ms, rf in regs:
                for MU, M_ in itertools.product(MUs, Ms):
                    base, alts = self.terms(t_, self.alpha, vsg, MU, M_)
                    base = base - self.delta * rf(MU, M_) * 2
                    self.certify(f"FD1 t={t_} {lab}", base, alts)
    def chains(self):
        a = self.a; R = self.R; Q = self.Qf; bpar = a % 2; one = self.one
        anti_last = tuple(-((-1) ** bpar) * v for v in self.sa)
        trunc = tuple([((-1) ** bpar) * v for v in self.sa][:-1] + [((-1) ** bpar) * self.sa[-1] - 2])
        self.ncheap = 0
        for g in self.vecs:
            if g[a] != -1 or g == anti_last: continue
            Dg = self.Delta[g]; ex = self.delta * 2 - Dg; sgn = ex.sign()
            if g == trunc:
                self.cnt('EQ')
                if ex.n: self.fails.append(("EQ Delta(trunc) != 2 delta", R.name))
                continue
            if sgn in (0, -1):
                self.cnt('EQ')
                if sgn == 0: self.fails.append((f"EQ other column with Delta = 2delta {g}", R.name))
                continue
            self.ncheap += 1
            v = self.Mv[g]; vsg = self.sg[g]
            for k in range(self.K + 1):
                idx_even = (k % 2 == 0) if bpar == 0 else (k % 2 == 1)
                allow_one = ((k + 1) % 2 == bpar) and not (k == 0 and bpar == 0)
                M_ = one if k == 0 else self.f(one, k)
                ys = ([self.mu0, self.L] if idx_even else [self.L, self.mu1]) + ([one] if allow_one else [])
                for Y0 in ys:
                    rho = self.f(Y0, k + 1)
                    chain = const(R, 0)
                    for i in range(1, k + 1): chain = chain + (Q * (self.f(Y0, k + 1 - i) + 1)).div_q()
                    chain = chain * Dg
                    eps = 1 if k % 2 == 0 else -1
                    cont = tuple(-eps * x for x in g)
                    for c in self.vecs:
                        if c == cont: continue
                        tv = tuple(eps * x for x in c)
                        base, alts = self.terms(tv, v, vsg, Y0, M_)
                        base = base + chain - ex * rho
                        self.certify(f"CH g={g} k={k} t={tv}", base, alts)
            idx_even = (self.K % 2 == 0) if bpar == 0 else (self.K % 2 == 1)
            for Y0 in ([self.mu0, self.L] if idx_even else [self.L, self.mu1]):
                chain = const(R, 0)
                for i in range(1, self.K + 2): chain = chain + (Q * (self.f(Y0, self.K + 1 - i) + 1)).div_q()
                e = chain * Dg - ex * self.f(Y0, self.K + 1)
                self.cnt('CHalone')
                if e.sign() != 1: self.fails.append((f"CH g={g} chain-alone", R.name))
            q_ = Q + 1
            d1 = (q_ * 3 - 4).div_q(); d2 = (q_ * q_ * 5 - q_ * 8 + 4).div_q(2)
            # Dhat_b / rho_b lower bounds, written without division by mu's:  Dg*Dhat - 2 delta rho > 0  <=  Dg*(D_low) - 2 delta * rho_high > 0
            conds = [Dg * (d1 + self.mu1 * 2) - self.delta * self.mu1 * 2] if bpar == 0 else \
                    [Dg * d1 - self.delta * self.mu0 * 2, Dg * (d2 + self.L * 2) - self.delta * self.L * 2]
            for e in conds:
                self.cnt('full')
                if e.sign() != 1: self.fails.append((f"CH g={g} full chain", R.name))
    def eq_forcing(self):
        a = self.a; R = self.R; bpar = a % 2; Qm = R.Q0
        g = tuple([((-1) ** bpar) * v for v in self.sa][:-1] + [((-1) ** bpar) * self.sa[-1] - 2])
        v = self.Mv[g]; vsg = self.sg[g]
        wrong = tuple(((-1) ** bpar) * x for x in self.sa); right = tuple(-x for x in wrong)
        self.cnt('EQ')
        if not any(self.sg[wrong][i] != 0 and vsg[i] != 0 and self.sg[wrong][i] * vsg[i] > 0 for i in range(a + 1)):
            self.fails.append(("EQ forcing", R.name))
        # referee-2 finding F1: certify directly s(wrong) > 0 at state g_trunc (m = 1) on the whole mu-range of column b-1,
        # mu = mu_{b-2}: b even -> [mu0, L]; b odd -> [L, mu1] (b >= 3) or mu = 1 (b = 1).  s is concave in mu -> endpoints.
        mus = [self.mu0, self.L] if bpar == 0 else [self.L, self.mu1, self.one]
        for MU in mus:
            base, alts = self.terms(wrong, v, vsg, MU, self.one)
            self.certify("EQwrong", base, alts)
        for i in range(a + 1):
            if vsg[i] == 0: continue
            self.cnt('EQ')
            if self.sg[right][i] * vsg[i] > 0: self.fails.append(("EQ right-choice sign", R.name)); continue
            if (self.absMv[right][i] * Qm - v[i] * vsg[i]).sign() not in (0, 1): self.fails.append(("EQ right-choice bound", R.name))
    def run(self):
        t0 = time.time(); cheap = {}
        for rname in ('big', 'p3'):
            self.setup(rname); self.lemmaS(); self.FD1(); self.chains(); self.eq_forcing(); cheap[rname] = self.ncheap
        print(f"a={self.a} K={self.K}: counts {self.counts}; cheap last columns {cheap}; failures {len(self.fails)} ({time.time()-t0:.0f}s)")
        for f in self.fails[:20]: print("   FAIL:", f)
        sys.stdout.flush()
        return not self.fails

if __name__ == "__main__":
    a = int(sys.argv[1]); K = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    FastProver(a, K).run()
