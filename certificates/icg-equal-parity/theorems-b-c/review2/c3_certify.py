"""Referee-2 independent re-certification of the per-a inequality list of PROOF.md sec. 11 (S_a, FD1_a, CH_a, EQ_a).

Independent of generic_prover.py: own matrices (r2poly.T_region), own exact rational-function arithmetic and own certified-sign
test (r2poly), and -- the main difference -- the surplus is NOT taken from the uniform formula but expanded directly from the
cell DEFINITION
    q*s(c, zeta) = Q(1+mu) Delta(c) - sum_i h_mu(A_i, B_i),   A = M c,  B = M zeta,
    -h_mu(A,B)   = -Q|A-B| - mu|B+QA| + (Q-mu)|B| + Q(1+mu)|A|,
where |A|, |B| have certified signs and each |A-B|, |B+QA| whose sign is not certified on the region is split into its two
branches (-|X| = min(X, -X), so checking all branches is exact).  Vertex reduction: for fixed m the expression is affine in mu,
for fixed mu it is concave in m (B = m*eps*v is linear in m, m > 0), and rho / chain costs are affine in the parameters, so
positivity at the box vertices implies positivity on the box.

Usage: python3 c3_certify.py a [K]
"""
import itertools, sys, time
from fractions import Fraction as Fr
from r2poly import Region, RF, T_region

a = int(sys.argv[1]) if len(sys.argv) > 1 else 3
K = int(sys.argv[2]) if len(sys.argv) > 2 else 4
VALN = int(sys.argv[3]) if len(sys.argv) > 3 else 400
NEED = Fr(sys.argv[4]) if len(sys.argv) > 4 else Fr(1)      # negative control: scale all needs
REGIONS = sys.argv[5].split(',') if len(sys.argv) > 5 else ['big', 'p3']
VALRATE = float(sys.argv[6]) if len(sys.argv) > 6 else 1.0
TAG = '' if (NEED == 1 and REGIONS == ['big', 'p3']) else f'_nc_{sys.argv[4]}_{"-".join(REGIONS)}'.replace('/', 'o')
LOG = open(f'logs/c3_certify_a{a}{TAG}.log', 'w')
def log(*x):
    s = ' '.join(str(y) for y in x); print(s); LOG.write(s + '\n'); LOG.flush()

t0 = time.time()
stats = {'S': 0, 'FD1': 0, 'CH': 0, 'CHalone': 0, 'full': 0, 'EQ': 0}
fails = []
sa = tuple((-1) ** i for i in range(a + 1))
vecs = list(itertools.product([1, -1], repeat=a + 1))
bpar = a % 2

def neg(v): return tuple(-x for x in v)

for rname in REGIONS:
    R = Region(rname)
    Qmin = R.Q0
    M = T_region(R, a)
    Mv = {c: [sum((M[i][k] * c[k] for k in range(a + 1)), R.const(0)) for i in range(a + 1)] for c in vecs}
    sg = {c: [x.sign() for x in Mv[c]] for c in vecs}
    for c in vecs:
        assert all(z is not None for z in sg[c]), ("undetermined sign of (Mc)_i", rname, c)
    absMv = {c: [Mv[c][i] * sg[c][i] for i in range(a + 1)] for c in vecs}
    alpha = Mv[sa]
    delta = alpha[a]
    Dtot = sum(absMv[sa], R.const(0))
    Delta = {c: Dtot - sum(absMv[c], R.const(0)) for c in vecs}
    Q = R.QQ()
    one = R.const(1)
    q = Q + 1
    mu0 = (Q - 1).div_q(); mu1 = (Q * Q + 1).div_q(2); Lb = Q.div_q1()
    def step(y): return (Q - y).div_q()          # mu_j = (Q - mu_{j-1})/q
    def it(y, n):
        for _ in range(n): y = step(y)
        return y

    # ---------------- S_a (crude bound at Q = Qmin, mu = 1; mu = 0 endpoint is Q*Delta(c) > 0) ----------------
    rowsum = [sum((M[i][k].absval() for k in range(a + 1)), R.const(0)) for i in range(a + 1)]
    for c in vecs:
        terms = []
        for i in range(a + 1):
            x = rowsum[i] - absMv[c][i] * Qmin
            s_ = x.sign()
            if s_ in (0, -1): continue
            terms.append([x] if s_ == 1 else [R.const(0), x])
        base = Delta[c] * (2 * Qmin)
        alt = c in (sa, neg(sa))
        for combo in itertools.product(*terms):
            e = base - 2 * sum(combo, R.const(0))
            stats['S'] += 1
            se = e.sign()
            if alt:
                if not (se == 0): fails.append(('S alt', rname, c))
            else:
                if se != 1: fails.append(('S', rname, c))
        # also: Delta(c) > 0 certified for non-alternating c (mu = 0 endpoint)
        if not alt and Delta[c].sign() != 1: fails.append(('Delta>0', rname, c))
        if alt and Delta[c].sign() != 0: fails.append(('Delta alt', rname, c))

    # ---------------- direct-form surplus: list of branch RFs of q*s ----------------
    def qs_branches(tvec, v, vsg, MU, m):
        """q*s(tvec at state m*v) with v = M g (entries RF with signs vsg), all branches (exact min)."""
        A = Mv[tvec]; As = sg[tvec]
        base = Q * (MU + 1) * Delta[tvec]
        parts = []
        for i in range(a + 1):
            B = m * v[i]
            absB = B * vsg[i] if vsg[i] != 0 else R.const(0)
            absA = absMv[tvec][i]
            base = base + (Q - MU) * absB + Q * (MU + 1) * absA
            X1 = A[i] - B
            X2 = B + Q * A[i]
            opts1 = []
            s1 = X1.sign()
            opts1 = [X1 * (-Q) * s1] if s1 is not None else [X1 * (-1) * Q, X1 * Q]      # -Q|X1|
            s2 = X2.sign()
            opts2 = [X2 * (-1) * MU * s2] if s2 is not None else [X2 * (-1) * MU, X2 * MU]  # -mu|X2|
            if len(opts1) * len(opts2) == 1:
                base = base + opts1[0] + opts2[0]
            else:
                parts.append([o1 + o2 for o1 in opts1 for o2 in opts2])
        out = []
        for combo in itertools.product(*parts):
            out.append(base + sum(combo, R.const(0)))
        return out

    import random as _r
    from r2core import T as _Tn, dd as _ddn, de as _den, surplus_direct as _sd
    _rv = _r.Random(777 + a)
    _numcache = {}
    def _num(s0, t0_):
        key = (s0, t0_)
        if key not in _numcache:
            Pn = R.P0 + s0; Qn = R.Q0 + t0_; pn = Pn + 1
            _numcache[key] = (Pn, Qn, _Tn(a, pn), _ddn(a, pn), _den(a, pn))
        return _numcache[key]
    def certify(name, exprs, key, direct=None):
        for e in exprs:
            stats[key] += 1
            if e.sign() != 1:
                fails.append((name, rname)); return False
        # end-to-end validation of the certified quantity at a random exact point (5% of the items)
        if direct is not None and _rv.random() < VALRATE:
            s0 = Fr(_rv.randint(0, 30), _rv.randint(1, 5)) if R.Pfree else Fr(0)
            t0_ = Fr(_rv.randint(0, 30), _rv.randint(1, 5))
            got = min(e.evalf(s0, t0_) for e in exprs)
            want = direct(s0, t0_)
            assert got == want, ('end-to-end validation', name, rname, float(got), float(want))
            stats['validated'] = stats.get('validated', 0) + 1
        return True

    # ---------------- FD1_a ----------------
    if bpar == 0:
        regs = [('R0', [one], [mu0, Lb], lambda MU, m: (Q - m).div_q()),
                ('R1', [mu0, Lb], [one], lambda MU, m: (Q - MU).div_q()),
                ('R2a', [Lb, mu1], [mu0, Lb], lambda MU, m: MU),
                ('R2b', [mu0, Lb], [Lb, mu1], lambda MU, m: m)]
    else:
        regs = [('B1', [one], [one], lambda MU, m: mu0),
                ('R0', [one], [Lb, mu1], lambda MU, m: (Q - m).div_q()),
                ('R1', [Lb, mu1], [one], lambda MU, m: (Q - MU).div_q()),
                ('R2odd', [Lb, mu1], [Lb, mu1], lambda MU, m: Lb),
                ('R2even', [mu0, Lb], [mu0, Lb], lambda MU, m: Lb)]
    asg = sg[sa]
    for tvec in vecs:
        if tvec == neg(sa): continue
        for lab, MUs, Ms, rf in regs:
            for MU, m in itertools.product(MUs, Ms):
                exprs = [e - q * delta * rf(MU, m) * (2 * NEED) for e in qs_branches(tvec, alpha, asg, MU, m)]
                def direct(s0, t0_, tvec=tvec, MU=MU, m=m, rf=rf):
                    Pn, Qn, Mn, Dn, dn = _num(s0, t0_); qn = Qn + 1
                    MUn, mn, rhon = MU.evalf(s0, t0_), m.evalf(s0, t0_), rf(MU, m).evalf(s0, t0_)
                    return qn * _sd(Mn, Dn, Qn, qn, MUn, list(tvec), [mn * x for x in sa]) - qn * dn * rhon * 2 * NEED
                certify(f'FD1 {tvec} {lab}', exprs, 'FD1', direct)

    # ---------------- last columns: classification, chains, EQ ----------------
    anti_last = tuple(-((-1) ** bpar) * x for x in sa)
    trunc_last = tuple(list(((-1) ** bpar) * x for x in sa)[:-1] + [((-1) ** bpar) * sa[-1] - 2])
    cheap = []; big = []
    for g in vecs:
        if g[a] != -1 or g == anti_last: continue
        ex = delta * (2 * NEED) - Delta[g]
        se = ex.sign()
        if g == trunc_last:
            stats['EQ'] += 1
            if se != 0: fails.append(('Delta(trunc) != 2 delta', rname))
            continue
        if se == -1:
            big.append(g); continue
        if se == 0:
            fails.append(('another column with Delta = 2 delta', rname, g)); continue
        cheap.append((g, se))
        v = Mv[g]; vsg = sg[g]
        for k in range(0, K + 1):
            idx_even = (k % 2 == 0) if bpar == 0 else (k % 2 == 1)
            ys = [mu0, Lb] if idx_even else [Lb, mu1]
            if (k + 1) % 2 == bpar and not (k == 0 and bpar == 0):
                ys = ys + [one]                                 # b = k + 1: y = mu_{-1} = 1
            m = it(one, k)                                      # mu_{k-1}
            eps = 1 if k % 2 == 0 else -1
            cont = tuple(-eps * x for x in g)
            for y in ys:
                rho = it(y, k + 1)
                chain = sum(((Q * (it(y, n) + 1)).div_q() for n in range(1, k + 1)), R.const(0)) * Delta[g]
                for c in vecs:
                    if c == cont: continue
                    tvec = tuple(eps * x for x in c)
                    exprs = [e + q * chain - q * ex * rho for e in qs_branches(tvec, v, vsg, y, m)]
                    def direct(s0, t0_, tvec=tvec, y=y, m=m, g=g, k=k):
                        # independent numeric recomputation: potentials by iterating the recursion numerically
                        Pn, Qn, Mn, Dn, dn = _num(s0, t0_); qn = Qn + 1
                        yn = y.evalf(s0, t0_); mn = Fr(1)
                        for _ in range(k): mn = (Qn - mn) / qn
                        mus_ = [yn]
                        for _ in range(k + 1): mus_.append((Qn - mus_[-1]) / qn)
                        Dg = Dn - sum(abs(sum(Mn[i][kk] * g[kk] for kk in range(a + 1))) for i in range(a + 1))
                        chain_n = sum(Qn * (1 + mus_[n]) / qn for n in range(1, k + 1)) * Dg
                        rho_n = mus_[k + 1]
                        sn = _sd(Mn, Dn, Qn, qn, yn, list(tvec), [mn * x for x in g])
                        return qn * sn + qn * chain_n - qn * (2 * NEED * dn - Dg) * rho_n
                    certify(f'CH g={g} k={k} c={c}', exprs, 'CH', direct)
        # chain alone, k >= K+1
        idx_even = (K % 2 == 0) if bpar == 0 else (K % 2 == 1)
        for y in ([mu0, Lb] if idx_even else [Lb, mu1]):
            chain = sum(((Q * (it(y, n) + 1)).div_q() for n in range(0, K + 1)), R.const(0)) * Delta[g]
            certify(f'CH alone g={g}', [chain - ex * it(y, K + 1)], 'CHalone')
        # full chain: Delta(g) Dhat_b > 2 delta rho_b via Dhat_b/rho_b >= ...
        D1 = (q * 3 - 4).div_q(); D2 = (q * q * 5 - q * 8 + 4).div_q(2)
        if bpar == 0:
            certify(f'full g={g}', [Delta[g] * D1 * q * q + (Delta[g] - delta) * 2 * (Q * Q + 1)], 'full')
            # (Delta*(D1/mu1 + 2) - 2 delta) * mu1 * q^2 = Delta*D1*q^2 + (2 Delta - 2 delta)(Q^2+1)
        else:
            certify(f'full b=1 g={g}', [Delta[g] * D1 * q - delta * 2 * (Q - 1)], 'full')
            # (Delta*D1/mu0 - 2 delta) * mu0 * q = Delta*D1*q - 2 delta (Q-1)
            certify(f'full b>=3 g={g}', [Delta[g] * D2 * (q + 1) + (Delta[g] * 2 - delta * 2) * Q], 'full')
            # (Delta*(D2/L + 2) - 2 delta) * L * (q+1) = Delta*D2*(q+1) + (2 Delta - 2 delta) Q

    # ---------------- EQ forcing at the truncated column ----------------
    g = trunc_last; v = Mv[g]; vsg = sg[g]
    wrong = tuple(((-1) ** bpar) * x for x in sa)          # (-1)^b s_a
    right = neg(wrong)                                       # Y+ column b-1 = (-1)^{b-1} s_a
    # mu at column b-1 is mu_{b-2}: b even -> [mu0, L];  b odd -> b = 1: 1, b >= 3: [L, mu1]
    MUs = [mu0, Lb] if bpar == 0 else [one, Lb, mu1]
    for MU in MUs:
        certify('EQ wrong choice s > 0', qs_branches(wrong, v, vsg, MU, one), 'EQ')
    A = Mv[right]; As = sg[right]
    for i in range(a + 1):
        stats['EQ'] += 1
        if vsg[i] == 0: continue
        if As[i] == 0 or As[i] * vsg[i] > 0: fails.append(('EQ right sign', rname, i)); continue
        if (absMv[right][i] * Qmin - v[i] * vsg[i]).sign() not in (0, 1): fails.append(('EQ right bound', rname, i))
    # ---------------- validation of the RF machinery against the direct Fraction computation (r2core) ----------------
    import random
    from r2core import T as Tnum, dd as ddn, de as den, surplus_direct, matvec as mvn
    rnd = random.Random(12345 + a)
    nval = 0
    for trial in range(VALN):
        s0 = Fr(rnd.randint(0, 60), rnd.randint(1, 7)) if R.Pfree else Fr(0)
        t0_ = Fr(rnd.randint(0, 60), rnd.randint(1, 7))
        Pn = R.P0 + s0; Qn = R.Q0 + t0_
        pn, qn = Pn + 1, Qn + 1
        Mn = Tnum(a, pn); Dn = ddn(a, pn); dn = den(a, pn)
        assert delta.evalf(s0, t0_) == dn and Dtot.evalf(s0, t0_) == Dn
        g = rnd.choice(vecs); c = rnd.choice(vecs)
        MU = rnd.choice([one, mu0, mu1, Lb, it(mu0, 3), it(Lb, 2)]); m = rnd.choice([one, mu0, mu1, Lb, it(one, 3)])
        MUn = MU.evalf(s0, t0_); mn = m.evalf(s0, t0_)
        val = min(e.evalf(s0, t0_) for e in qs_branches(c, Mv[g], sg[g], MU, m))
        dirv = qn * surplus_direct(Mn, Dn, Qn, qn, MUn, list(c), [mn * x for x in g])
        assert val == dirv, ('validation', rname, g, c)
        assert Delta[g].evalf(s0, t0_) == Dn - sum(abs(x) for x in mvn(Mn, list(g)))
        nval += 1
    log(f"a={a} region={rname}: validated q*s branch-min against direct cell computation at {nval} random exact points: OK")
    log(f"a={a} region={rname}: cheap last columns {[(g, s_) for g, s_ in cheap]}; columns with Delta > 2 delta: {len(big)}; "
        f"trunc = {trunc_last}")

log(f"a={a} K={K}: checks {stats}; failures {len(fails)}; time {time.time() - t0:.0f}s")
for f in fails[:40]:
    log("  FAIL", f)
