"""Referee-3 independent certifier for the hypotheses (S_a), (F_a), (C_a) of Proposition 31 of Paper 1 (note.tex v1.4,
label prop:reduction), for one exponent a >= 2.

Written from the TEXT of Proposition 31; it imports nothing from generic_prover*.py, generic_fast2.py or review2/.
Paper notation: x = q, P = q - 1, R = p - 1, M = T_a(p), alpha = M s_a, delta_a = alpha_a, omega_i = sum_k |M_ik|,
Delta(c) = d_a(p) - ||Mc||_1, psi_mu(c, zeta) = P(1+mu) Delta(c) - sum_i h_mu((Mc)_i, (M zeta)_i),
h_mu(A,B) = P|A-B| + mu|B+PA| - (P-mu)|B| - P(1+mu)|A|  (Lemma 10 with P = x - 1), eta(y) = (P - y)/x.

Design differences from the two existing implementations:
  * T_a(p) is built from the Ramanujan-sum definition t_ij = phi(p^{a-i}) c_{p^{a-j}}(p^i) with symbolic p, compared with the
    closed formula of Section 2 coefficient by coefficient, and with genuine Ramanujan sums at p = 3, 5, 7.
  * The task list is enumerated from Proposition 31 as printed (the families of F_a, the sets I_k of (C1), (C2), (C3)).
  * A cell is evaluated with the case table of the proof of Lemma 10 (four cases for A != 0, and h(0,B) = 2 mu |B|); the case
    is chosen by a CERTIFIED sign comparison (m|v_i| vs |A_i| when A_i and B_i have the same sign, m|v_i| vs P|A_i| when they
    have opposite signs).  Only when that comparison is not certified on the region are both case formulas kept; the true
    value is one of them (it is in fact their minimum), so requiring every choice to be positive is sound.  The state sign is
    kept in the cell (the column is not renormalised).
  * Arithmetic: each term is (t-polynomial over q^K (q+1)^L) x (s-polynomial) x integer; per parameter vertex all terms are
    brought to one denominator and expanded into flat integer arrays.  Python integers only (no overflow).
  * A fraction --val of the certified items is validated end to end at a random exact point against a direct evaluation from
    the definitions (closed-form T_a(p) in Fractions, mu by recursion, h by its definition).

Regions (Proposition 31): R1: p = 5 + s, q = 3 + t (s, t >= 0), P_min = 2;  R2: p = 3, q = 5 + t (t >= 0), P_min = 4.
Certified sign of a polynomial in s,t >= 0: +1 if all coefficients >= 0 and the constant term > 0, -1 symmetrically, 0 if
identically 0, else None (undetermined).  Denominators are powers of q and q + 1, positive on the region.

Negative-control switches: --need X (replace 2 delta_a by 2 X delta_a, i.e. try to certify G <= d_a d_b - 2 X delta_a delta_b;
g_+ is then treated as an ordinary last column), --bpar 0/1 (parity of b; default a mod 2), --regions (R1, R2 or enlarged
regions: E33 p = q = 3, EQ2 p >= 5 & q >= 2, E3Q4 p = 3 & q >= 4, EP4 p >= 4 & q >= 3), --K (chain depth, default 4 as in
Proposition 31).  --sample F keeps each item with probability F (fixed seed) for sampled runs.
"""
import argparse, itertools, random, sys, time
from fractions import Fraction as Fr
from math import gcd

ap = argparse.ArgumentParser()
ap.add_argument('a', type=int)
ap.add_argument('--K', type=int, default=4)
ap.add_argument('--need', type=Fr, default=Fr(1))
ap.add_argument('--bpar', type=int, default=None)
ap.add_argument('--regions', default='R1,R2')
ap.add_argument('--sample', type=float, default=1.0)
ap.add_argument('--seed', type=int, default=20260926)
ap.add_argument('--val', type=float, default=0.02, help='fraction of certified items validated at a random exact point')
ap.add_argument('--log', default=None)
ap.add_argument('--maxfail', type=int, default=40)
ap.add_argument('--skip-gplus', action='store_true', help='margin probe: keep g_+ (the column of Y^+) excluded when --need != 1')
args = ap.parse_args()
a = args.a
K = args.K
NEED = args.need
NUM, DEN = NEED.numerator, NEED.denominator
BPAR = (a % 2) if args.bpar is None else args.bpar
LOG = open(args.log, 'w') if args.log else None


def log(*xs):
    s = ' '.join(str(x) for x in xs)
    print(s)
    sys.stdout.flush()
    if LOG:
        LOG.write(s + '\n')
        LOG.flush()


# ---------------------------------------------------------------- univariate integer polynomials (lists, index = degree)
def u_trim(x):
    while x and x[-1] == 0:
        x.pop()
    return x


def u_add(x, y, cy=1):
    r = [0] * max(len(x), len(y))
    for i, v in enumerate(x):
        r[i] += v
    for i, v in enumerate(y):
        r[i] += cy * v
    return u_trim(r)


def u_mul(x, y):
    if not x or not y:
        return []
    r = [0] * (len(x) + len(y) - 1)
    for i, u in enumerate(x):
        if u:
            for j, v in enumerate(y):
                r[i + j] += u * v
    return u_trim(r)


def u_scale(x, c):
    return u_trim([c * v for v in x]) if c else []


def u_pow(x, n):
    r = [1]
    for _ in range(n):
        r = u_mul(r, x)
    return r


def u_sign(x):
    if not x:
        return 0
    if x[0] > 0 and all(v >= 0 for v in x):
        return 1
    if x[0] < 0 and all(v <= 0 for v in x):
        return -1
    return None


def u_eval(x, z):
    r = Fr(0)
    for v in reversed(x):
        r = r * z + v
    return r


# ---------------------------------------------------------------- regions
REGIONS = {   # name: (p as a polynomial in s, q as a polynomial in t, P_min, description)
    'R1': ([5, 1], [3, 1], 2, 'p = 5+s, q = 3+t'),
    'R2': ([3], [5, 1], 4, 'p = 3, q = 5+t'),
    'E33': ([3], [3], 2, 'p = q = 3 [negative control]'),
    'EQ2': ([5, 1], [2, 1], 1, 'p = 5+s, q = 2+t [negative control]'),
    'E3Q4': ([3], [4, 1], 3, 'p = 3, q = 4+t [negative control]'),
    'EP4': ([4, 1], [3, 1], 2, 'p = 4+s, q = 3+t [negative control]'),
}


class Region:
    def __init__(self, name):
        self.name = name
        self.p, self.q, self.Pmin, self.desc = REGIONS[name]
        self.P = u_add(self.q, [-1])
        self.q1 = u_add(self.q, [1])
        self._qp, self._q1p = {0: [1]}, {0: [1]}

    def qpow(self, n):
        if n not in self._qp:
            self._qp[n] = u_mul(self.qpow(n - 1), self.q)
        return self._qp[n]

    def q1pow(self, n):
        if n not in self._q1p:
            self._q1p[n] = u_mul(self.q1pow(n - 1), self.q1)
        return self._q1p[n]


class QR:
    """a rational function of q only: n(t) / (q^K (q+1)^L)."""
    __slots__ = ('n', 'K', 'L', 'k')

    def __init__(self, n, K=0, L=0):
        self.n, self.K, self.L = u_trim(list(n)), K, L
        self.k = (tuple(self.n), K, L)


def q_lift(R, x, K_, L_):
    n = x.n
    if K_ > x.K:
        n = u_mul(n, R.qpow(K_ - x.K))
    if L_ > x.L:
        n = u_mul(n, R.q1pow(L_ - x.L))
    return n


def q_add(R, x, y, cy=1):
    K_, L_ = max(x.K, y.K), max(x.L, y.L)
    return QR(u_add(q_lift(R, x, K_, L_), q_lift(R, y, K_, L_), cy), K_, L_)


def q_mul(x, y):
    return QR(u_mul(x.n, y.n), x.K + y.K, x.L + y.L)


def q_eval(R, x, t0):
    qv = u_eval(R.q, t0)
    return u_eval(x.n, t0) / (qv ** x.K * (qv + 1) ** x.L)


class Ctx:
    """common denominator q^KC (q+1)^LC and array shape for all terms of one parameter vertex."""
    _id = 0

    def __init__(self, R, qrs, degS):
        self.R = R
        self.KC = max(x.K for x in qrs)
        self.LC = max(x.L for x in qrs)
        dq, dq1 = len(R.q) - 1, len(R.q1) - 1
        self.W = max(len(x.n) + (self.KC - x.K) * dq + (self.LC - x.L) * dq1 for x in qrs)
        self.H = degS + 1
        self.size = self.H * self.W
        self.lcache = {}
        Ctx._id += 1
        self.id = Ctx._id

    def arr(self, terms):
        B = [0] * self.size
        W = self.W
        for x, sp, cf in terms:
            if not sp or not cf or not x.n:
                continue
            tn = self.lcache.get(x.k)
            if tn is None:
                assert x.K <= self.KC and x.L <= self.LC, 'context too small'
                tn = self.lcache[x.k] = q_lift(self.R, x, self.KC, self.LC)
                assert len(tn) <= W
            assert len(sp) <= self.H, 'context too small (s-degree)'
            for i, sv in enumerate(sp):
                if sv:
                    m_ = cf * sv
                    base = i * W
                    for j, tv in enumerate(tn):
                        if tv:
                            B[base + j] += m_ * tv
        return B

    def value(self, B, s0, t0):
        W = self.W
        num = Fr(0)
        for i in range(self.H):
            num += Fr(s0) ** i * u_eval(B[i * W:(i + 1) * W], t0)
        qv = u_eval(self.R.q, t0)
        return num / (qv ** self.KC * (qv + 1) ** self.LC)


def a_sign(B):
    """certified sign of the numerator array; B[0] is the constant term."""
    c0 = B[0]
    if c0 > 0:
        return 1 if min(B) >= 0 else None
    if c0 < 0:
        return -1 if max(B) <= 0 else None
    return 0 if not any(B) else None


def a_sum(arrs):
    if len(arrs) == 1:
        return arrs[0]
    return [sum(z) for z in zip(*arrs)]


# ---------------------------------------------------------------- T_a(p)
def matrix_ramanujan(k, p):
    """t_ij = phi(p^{k-i}) c_{p^{k-j}}(p^i), p a polynomial; c_{p^e}(p^i) = phi(p^e) if e <= i, -p^{e-1} if e = i + 1,
    0 if e >= i + 2 (c_1 = 1)."""
    pm1 = u_add(p, [-1])

    def phi(e):
        return [1] if e == 0 else u_mul(u_pow(p, e - 1), pm1)

    def ram(e, i):
        if e == 0:
            return [1]
        if e <= i:
            return phi(e)
        if e == i + 1:
            return u_scale(u_pow(p, e - 1), -1)
        return []

    return [[u_mul(phi(k - i), ram(k - j, i)) for j in range(k + 1)] for i in range(k + 1)]


def matrix_closed(k, p):
    pm1 = u_add(p, [-1])
    M = [[None] * (k + 1) for _ in range(k + 1)]
    for i in range(k + 1):
        for j in range(k + 1):
            if i < k and j < k:
                if i + j <= k - 2:
                    v = []
                elif i + j == k - 1:
                    v = u_scale(u_mul(u_pow(p, k - 1), pm1), -1)
                else:
                    v = u_mul(u_pow(p, 2 * k - i - j - 2), u_mul(pm1, pm1))
            elif i == k and j == k:
                v = [1]
            else:
                tt = i if i < k else j
                v = u_mul(u_pow(p, k - tt - 1), pm1)
            M[i][j] = v
    return M


def Tnum(k, x):
    x = Fr(x)
    M = [[Fr(0)] * (k + 1) for _ in range(k + 1)]
    for i in range(k + 1):
        for j in range(k + 1):
            if i < k and j < k:
                if i + j <= k - 2:
                    v = 0
                elif i + j == k - 1:
                    v = -x ** (k - 1) * (x - 1)
                else:
                    v = x ** (2 * k - i - j - 2) * (x - 1) ** 2
            elif i == k and j == k:
                v = 1
            else:
                tt = i if i < k else j
                v = x ** (k - tt - 1) * (x - 1)
            M[i][j] = Fr(v)
    return M


def moeb(n):
    r, d, m = 1, 2, n
    while d * d <= m:
        if m % d == 0:
            m //= d
            if m % d == 0:
                return 0
            r = -r
        d += 1
    return -r if m > 1 else r


def cram(m, n):
    g = gcd(m, n)
    return sum(moeb(m // d) * d for d in range(1, g + 1) if g % d == 0)


def h_def(P, mu, A, B):
    return P * abs(A - B) + mu * abs(B + P * A) - (P - mu) * abs(B) - P * (1 + mu) * abs(A)


# ---------------------------------------------------------------- main
t_start = time.time()
rng = random.Random(args.seed + 1000 * a + 7 * BPAR)
vrng = random.Random(args.seed + 17 * a)
sa = tuple((-1) ** i for i in range(a + 1))
vecs = list(itertools.product([1, -1], repeat=a + 1))


def neg(v):
    return tuple(-z for z in v)


stats = {}
fails = []


def bump(k_, n=1):
    stats[k_] = stats.get(k_, 0) + n


log(f'rv3_certify a={a} K={K} need={NEED} bpar={BPAR} regions={args.regions} sample={args.sample} seed={args.seed} '
    f'val={args.val}  started {time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}')

# the matrix: symbolic Ramanujan construction == closed formula; numeric Ramanujan sums at p = 3, 5, 7
for pr in (3, 5, 7):
    Mn = matrix_ramanujan(a, [pr])
    for i in range(a + 1):
        for j in range(a + 1):
            ph = 1 if a - i == 0 else pr ** (a - i - 1) * (pr - 1)
            assert (Mn[i][j][0] if Mn[i][j] else 0) == ph * cram(pr ** (a - j), pr ** i), ('Ramanujan mismatch', pr, i, j)
log(f'  T_{a}(p): symbolic Ramanujan-sum construction agrees with genuine Ramanujan sums at p = 3, 5, 7')

for rname in args.regions.split(','):
    R = Region(rname)
    M = matrix_ramanujan(a, R.p)
    Mcl = matrix_closed(a, R.p)
    assert all(M[i][j] == Mcl[i][j] for i in range(a + 1) for j in range(a + 1)), 'T_a: Ramanujan != closed formula'
    Av = {}
    for c in vecs:
        rows = []
        for i in range(a + 1):
            acc = []
            for k_ in range(a + 1):
                acc = u_add(acc, M[i][k_], c[k_])
            rows.append(acc)
        Av[c] = rows
    sgn = {}
    for c in vecs:
        ss = [u_sign(z) for z in Av[c]]
        if any(z is None for z in ss):
            log('ABORT: undetermined sign of (Mc)_i', rname, c)
            raise SystemExit(2)
        sgn[c] = ss
    absA = {c: [u_scale(Av[c][i], sgn[c][i]) for i in range(a + 1)] for c in vecs}
    Dtot = []
    for z in absA[sa]:
        Dtot = u_add(Dtot, z)
    Delta = {}
    for c in vecs:
        tot = []
        for z in absA[c]:
            tot = u_add(tot, z)
        Delta[c] = u_add(Dtot, tot, -1)
    alpha = Av[sa]
    delta = alpha[a]
    omega = []
    for i in range(a + 1):
        tot = []
        for k_ in range(a + 1):
            sg_ = u_sign(M[i][k_])
            assert sg_ is not None
            tot = u_add(tot, u_scale(M[i][k_], sg_ if sg_ else 1))
        omega.append(tot)
    for c in vecs:
        sd = u_sign(Delta[c])
        if c in (sa, neg(sa)):
            assert sd == 0
        elif sd != 1:
            fails.append(('Delta(c) > 0 not certified', rname, c))
    degS = max(len(z) for z in list(Delta.values()) + [x for c in vecs for x in absA[c]] + omega + [delta]) - 1
    degS = max(degS, 0)

    one = QR([1])
    Pq = QR(R.P)
    xq = QR(R.q)
    inv_q = QR([1], 1, 0)
    mu0 = QR(u_add(R.P, [-1]), 1, 0)
    mu1 = QR(u_add(u_mul(R.P, R.P), [1]), 2, 0)
    muinf = QR(R.P, 0, 1)

    def eta(y, n=1):
        for _ in range(n):
            y = q_mul(q_add(R, Pq, y, -1), inv_q)
        return y

    for t0 in (Fr(0), Fr(7, 3)):     # the closed forms of mu0, mu1, muinf and eta against the recursion
        qv = u_eval(R.q, t0)
        mus = {-1: Fr(1)}
        for j in range(4):
            mus[j] = (qv - 1 - mus[j - 1]) / qv
        assert q_eval(R, mu0, t0) == mus[0] and q_eval(R, mu1, t0) == mus[1]
        assert q_eval(R, muinf, t0) == (qv - 1) / (qv + 1) and q_eval(R, eta(one, 3), t0) == mus[2]

    _numc = {}

    def numctx(s0, t0):
        key = (s0, t0)
        if key not in _numc:
            pv, qv = u_eval(R.p, s0), u_eval(R.q, t0)
            Mn = Tnum(a, pv)
            Mcn = {c: [sum(Mn[i][j] * c[j] for j in range(a + 1)) for i in range(a + 1)] for c in vecs}
            Dn = sum(abs(z) for z in Mcn[sa])
            mus = {-1: Fr(1)}
            for j in range(12):
                mus[j] = (qv - 1 - mus[j - 1]) / qv
            if len(_numc) > 32:
                _numc.clear()
            _numc[key] = dict(p=pv, q=qv, P=qv - 1, M=Mn, Mc=Mcn,
                              Del={c: Dn - sum(abs(z) for z in Mcn[c]) for c in vecs}, mus=mus, delta=Mcn[sa][a])
        return _numc[key]

    def psi_direct(C, mu, c, coef, gvec):
        Mz = [coef * sum(C['M'][i][j] * gvec[j] for j in range(a + 1)) for i in range(a + 1)]
        return C['P'] * (1 + mu) * C['Del'][c] - sum(h_def(C['P'], mu, C['Mc'][c][i], Mz[i]) for i in range(a + 1))

    def certify(name, cat, ctx, det_arrs, cand_arrs, direct=None):
        if args.sample < 1.0 and rng.random() >= args.sample:
            bump('skipped_' + cat)
            return True
        bump('items_' + cat)
        B0 = a_sum(det_arrs) if det_arrs else [0] * ctx.size
        combos = list(itertools.product(*cand_arrs)) if cand_arrs else [()]
        tot = []
        for combo in combos:
            Bt = a_sum([B0] + list(combo)) if combo else B0
            bump('branches_' + cat)
            if a_sign(Bt) != 1:
                fails.append((cat, name, rname))
                return False
            tot.append(Bt)
        if direct is not None and vrng.random() < args.val:
            s0 = Fr(vrng.randint(0, 40), vrng.randint(1, 6)) if len(R.p) > 1 else Fr(0)
            t0 = Fr(vrng.randint(0, 40), vrng.randint(1, 6)) if len(R.q) > 1 else Fr(0)
            got = min(ctx.value(B, s0, t0) for B in tot)
            want = direct(s0, t0)
            assert got == want, ('VALIDATION MISMATCH', cat, name, rname, float(got), float(want))
            bump('validated_' + cat)
        return True

    # ---- cells ------------------------------------------------------------------------------------------------------------
    cmp_cache = {}

    def compare_sign(m, absv, coefA, aA):
        """certified sign of m|v| - coefA*|A| (m, coefA: QR)."""
        key = (m.k, tuple(absv), coefA.k, tuple(aA))
        r = cmp_cache.get(key)
        if r is None:
            qrs = [m, coefA]
            cx = Ctx(R, qrs, degS)
            r = a_sign(cx.arr([(m, absv, 1), (coefA, aA, -1)]))
            cmp_cache[key] = r
            bump('cmp_certified' if r is not None else 'cmp_split')
        return r

    cell_cache = {}

    def cell_arrs(ctx, c, i, gv, eps, m, mu):
        """candidate arrays for -h_mu((Mc)_i, eps * m * (M gv)_i) in the context ctx."""
        key = (ctx.id, c[max(0, a - 1 - i):], i, gv, eps)
        r = cell_cache.get(key)
        if r is not None:
            return r
        sA, sv = sgn[c][i], sgn[gv][i]
        aA = absA[c][i]
        absv = absA[gv][i]
        if sA == 0:
            cands = [[(q_mul(mu, m), absv, -2)]]                  # h(0, B) = 2 mu |B|
        elif sv == 0:
            cands = [[]]                                           # h(A, 0) = 0
        else:
            tau = sA * eps * sv
            if tau > 0:     # A' = |A|, B' = m|v| >= 0:  B' <= A': h = -2(P-mu)B';  B' > A': h = 2(mu B' - P A')
                sd = compare_sign(m, absv, one, aA)
                c1 = [(q_mul(q_add(R, Pq, mu, -1), m), absv, 2)]
                c2 = [(Pq, aA, 2), (q_mul(mu, m), absv, -2)]
            else:           # B' = -m|v| < 0:  |B'| <= P A': h = 0;  |B'| > P A': h = 2 mu (|B'| - P A')
                sd = compare_sign(m, absv, Pq, aA)
                c1 = []
                c2 = [(q_mul(mu, m), absv, -2), (q_mul(mu, Pq), aA, 2)]
            cands = [c1] if sd in (-1, 0) else ([c2] if sd == 1 else [c1, c2])
        r = [ctx.arr(cd) for cd in cands]
        if len(cell_cache) > 300000:
            cell_cache.clear()
        cell_cache[key] = r
        return r

    def psi_arrs(ctx, c, gv, eps, m, mu, scale):
        det = [ctx.arr([(q_mul(Pq, q_add(R, one, mu)), Delta[c], scale)])]
        cand = []
        for i in range(a + 1):
            cl = cell_arrs(ctx, c, i, gv, eps, m, mu)
            if scale != 1:
                cl = [[scale * z for z in B] for B in cl]
            if len(cl) == 1:
                det.append(cl[0])
            else:
                cand.append(cl)
        return det, cand

    def vertex_ctx(mu, m, extra):
        qrs = [one, Pq, q_mul(Pq, q_add(R, one, mu)), q_mul(mu, m), q_mul(q_add(R, Pq, mu, -1), m), q_mul(mu, Pq)] + extra
        return Ctx(R, qrs, degS)

    # ======================================== (S_a) ====================================================================
    Pm = R.Pmin
    for c in vecs:
        if c in (sa, neg(sa)):
            continue
        cx = Ctx(R, [one], degS)
        det = [cx.arr([(one, Delta[c], Pm)])]
        cand = []
        for i in range(a + 1):
            xi = u_add(omega[i], u_scale(absA[c][i], Pm), -1)
            sx = u_sign(xi)
            if sx in (-1, 0):
                continue
            if sx == 1:
                det.append(cx.arr([(one, xi, -1)]))
            else:
                cand.append([[0] * cx.size, cx.arr([(one, xi, -1)])])

        def dS(s0, t0, c=c):
            C = numctx(s0, t0)
            om = [sum(abs(z) for z in C['M'][i]) for i in range(a + 1)]
            return Pm * C['Del'][c] - sum(max(0, om[i] - Pm * abs(C['Mc'][c][i])) for i in range(a + 1))

        certify(f'S c={c}', 'S', cx, det, cand, dS)

    # ======================================== (F_a) ====================================================================
    if BPAR == 0:
        fams = [('F1', [one], [mu0, muinf], lambda mu, m: eta(m)),       # (1, m, (P-m)/x), m in [mu0, muinf]
                ('F2', [mu0, muinf], [one], lambda mu, m: eta(mu)),      # (mu, 1, (P-mu)/x), mu in [mu0, muinf]
                ('F3', [muinf, mu1], [mu0, muinf], lambda mu, m: mu),    # (mu, m, mu), mu in [muinf, mu1], m in [mu0, muinf]
                ('F4', [mu0, muinf], [muinf, mu1], lambda mu, m: m)]     # (mu, m, m), mu in [mu0, muinf], m in [muinf, mu1]
    else:
        fams = [('F0', [one], [one], lambda mu, m: mu0),                 # (1, 1, mu0)
                ('F1', [one], [muinf, mu1], lambda mu, m: eta(m)),       # (1, m, (P-m)/x), m in [muinf, mu1]
                ('F2', [muinf, mu1], [one], lambda mu, m: eta(mu)),      # (mu, 1, (P-mu)/x), mu in [muinf, mu1]
                ('F3', [mu0, muinf], [mu0, muinf], lambda mu, m: muinf), # (mu, m, muinf), mu, m in [mu0, muinf]
                ('F4', [muinf, mu1], [muinf, mu1], lambda mu, m: muinf)] # (mu, m, muinf), mu, m in [muinf, mu1]
    for fname, MUs, Ms, rfun in fams:
        for mu, m in itertools.product(MUs, Ms):
            r_ = rfun(mu, m)
            xr = q_mul(xq, r_)
            ctx = vertex_ctx(mu, m, [xr])
            rhs = ctx.arr([(xr, delta, -2 * NUM)])
            for c in vecs:
                if c == neg(sa):
                    continue
                det, cand = psi_arrs(ctx, c, sa, 1, m, mu, DEN)

                def dF(s0, t0, c=c, mu=mu, m=m, r_=r_):
                    C = numctx(s0, t0)
                    muv, mv, rv = q_eval(R, mu, t0), q_eval(R, m, t0), q_eval(R, r_, t0)
                    return DEN * psi_direct(C, muv, c, mv, sa) - 2 * NUM * C['q'] * C['delta'] * rv

                certify(f'F {fname} c={c} mu={mu.k} m={m.k}', 'F', ctx, det + [rhs], cand, dF)

    # ======================================== (C_a) ====================================================================
    anti = neg(tuple(((-1) ** BPAR) * z for z in sa))        # -(-1)^b s_a: last column of Y^-
    gplus = None
    if BPAR == a % 2:
        gp = [((-1) ** a) * z for z in sa]
        gp[a] -= 2
        gplus = tuple(gp)                                    # g_+ = (-1)^a s_a - 2 e_a
        assert set(gplus) <= {1, -1} and gplus[a] == -1
        bump('eq_identity_checked')
        if u_add(Delta[gplus], u_scale(delta, 2), -1):
            fails.append(('Delta(g_+) = 2 delta_a fails', rname))
    excluded = {anti} | ({gplus} if (gplus is not None and (NEED == 1 or args.skip_gplus)) else set())
    cheap, expensive = [], []
    D1 = QR(u_add(u_scale(R.q, 3), [-4]), 1, 0)                           # d_1(x)/x
    D2 = QR(u_add(u_add(u_scale(u_mul(R.q, R.q), 5), u_scale(R.q, -8)), [4]), 2, 0)   # d_2(x)/x^2
    for g in vecs:
        if g[a] != -1 or g in excluded:
            continue
        gam = u_add(u_scale(delta, 2 * NUM), u_scale(Delta[g], DEN), -1)    # DEN * gamma, gamma = 2 NEED delta - Delta(g)
        sg_ = u_sign(u_scale(gam, -1))                                     # certified sign of Delta(g) - 2 NEED delta
        if sg_ == 1:
            expensive.append(g)
            continue
        cheap.append((g, sg_))
        DgS = u_scale(Delta[g], DEN)
        # ---- (C1): 0 <= k <= K, y in I_k, c != (-1)^{k+1} g
        for k in range(K + 1):
            Ys = [mu0, muinf] if k % 2 == BPAR else [muinf, mu1, one]      # I_k
            m = eta(one, k)                                                # mu_{k-1}
            eps = (-1) ** k
            forb = tuple(((-1) ** (k + 1)) * z for z in g)
            for y in Ys:
                chainq = [q_mul(Pq, q_add(R, one, eta(y, n))) for n in range(1, k + 1)]
                xe = q_mul(xq, eta(y, k + 1))
                ctx = vertex_ctx(y, m, chainq + [xe])
                fixed = ctx.arr([(cq, DgS, 1) for cq in chainq] + [(xe, gam, -1)])
                for c in vecs:
                    if c == forb:
                        continue
                    det, cand = psi_arrs(ctx, c, g, eps, m, y, DEN)

                    def dC1(s0, t0, c=c, y=y, k=k, g=g, eps=eps):
                        C = numctx(s0, t0)
                        yv = q_eval(R, y, t0)
                        et = [yv]
                        for _ in range(k + 1):
                            et.append((C['P'] - et[-1]) / C['q'])
                        chain_v = sum(C['P'] * (1 + et[n]) for n in range(1, k + 1)) * C['Del'][g]
                        gam_v = 2 * NEED * C['delta'] - C['Del'][g]
                        return DEN * (chain_v + psi_direct(C, yv, c, eps * C['mus'][k - 1], g) - C['q'] * et[k + 1] * gam_v)

                    certify(f'C1 g={g} k={k} y={y.k} c={c}', 'C1', ctx, det + [fixed], cand, dC1)
        # ---- (C2): columns b-1, ..., b-K-1 of the chain alone; y = mu_{b-K-2}
        for y in ([mu0, muinf] if K % 2 == BPAR else [muinf, mu1]):
            chainq = [q_mul(Pq, q_add(R, one, eta(y, n))) for n in range(0, K + 1)]
            xe = q_mul(xq, eta(y, K + 1))
            ctx = Ctx(R, chainq + [xe, one], degS)
            certify(f'C2 g={g} y={y.k}', 'C2', ctx, [ctx.arr([(cq, DgS, 1) for cq in chainq] + [(xe, gam, -1)])], [])
        # ---- (C3): the whole column sequence is the chain
        two_delta = u_scale(delta, 2 * NUM)
        if BPAR == 0:       # Delta(g)(D1/mu1 + 2) > 2 delta  <=>  Delta(g)(D1 + 2 mu1) - 2 delta mu1 > 0
            ctx = Ctx(R, [D1, mu1, one], degS)
            certify(f'C3 g={g}', 'C3', ctx, [ctx.arr([(D1, DgS, 1), (mu1, DgS, 2), (mu1, two_delta, -1)])], [])
        else:               # Delta(g) D1 - 2 delta mu0 > 0  and  Delta(g)(D2 + 2 muinf) - 2 delta muinf > 0
            ctx = Ctx(R, [D1, mu0, one], degS)
            certify(f'C3(b=1) g={g}', 'C3', ctx, [ctx.arr([(D1, DgS, 1), (mu0, two_delta, -1)])], [])
            ctx = Ctx(R, [D2, muinf, one], degS)
            certify(f'C3(b>=3) g={g}', 'C3', ctx, [ctx.arr([(D2, DgS, 1), (muinf, DgS, 2), (muinf, two_delta, -1)])], [])
    log(f'  region {rname} ({R.desc}): cheap last columns ({len(cheap)}): {[g for g, _ in cheap]}')
    log(f'  region {rname}: last columns with Delta > 2 delta certified: {len(expensive)}; sign of Delta - 2 delta '
        f'undetermined for: {[g for g, s_ in cheap if s_ is None]}; g_+ = {gplus}; anti = {anti}')
    log(f'  region {rname}: done at {time.time() - t_start:.0f}s; failures so far {len(fails)}')

log(f'a={a} K={K} need={NEED} bpar={BPAR} regions={args.regions}: {dict(sorted(stats.items()))}')
log(f'FAILURES: {len(fails)}')
for f in fails[:args.maxfail]:
    log('  FAIL', f)
log(f'total time {time.time() - t_start:.1f}s')
