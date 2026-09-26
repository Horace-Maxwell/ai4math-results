"""(b) Lemma 4 at q = 3, adversarially.

Lambda(y,zeta) = P F(y-zeta) + mu F(zeta+P y) - (P-mu) F(zeta),  F(w) = ||T_b(3) w||_1.
Claim: Lambda <= P(1+mu) d_b(3), strict unless y = +-s_b  (P>=4, 3/5<=mu<=1, zeta in [-1,1]^{b+1}).

For fixed y, P the function zeta -> (F(y-zeta), F(zeta+Py), F(zeta)) is linear on each cell of
the arrangement {(T zeta)_r in {0, (Ty)_r, -P(Ty)_r}} restricted to the cube, so the max of
Lambda over the cube is attained at a vertex of this arrangement (intersection of b+1
independent hyperplanes among those and zeta_i = +-1).  Part 1 enumerates ALL such vertices
in float64 (b=1..6); the maximising vertex of every (P,mu,y) is then re-solved and re-evaluated
in exact Fractions (all maximisers for b<=5; the worst non-alternating and alternating for b=6).
Part 2 is random start + exact 1-D piecewise-linear line search (coordinate / random / pair
directions) for b=1..6, including random P, mu; best points re-evaluated exactly.
Also checks the intermediate per-term claims of the proof at every exactly-evaluated point.
"""
import sys, itertools, random, time
import numpy as np
from fractions import Fraction as Fr
from rv_core import T_gen, d_formula, zpath, mu_c, svec, matvec, l1

q = Fr(3)
random.seed(7)
rng = np.random.default_rng(7)
MODE = sys.argv[1] if len(sys.argv) > 1 else 'all'
BMAX_VERTEX = int(sys.argv[2]) if len(sys.argv) > 2 else 6


def exact_lambda(T, y, zeta, P, mu):
    F = lambda w: l1(matvec(T, w))
    return (P * F([a - b for a, b in zip(y, zeta)]) + mu * F([b + P * a for a, b in zip(y, zeta)])
            - (P - mu) * F(zeta))


def per_term_check(b, y, zeta, P, mu):
    """Check the proof's intermediate claims: h_j <= 0 for j notin NA (and j=-1),
    h_j < 2P(1+mu) mu^q_j x_j for j in NA, and the decomposition Lambda/q^b = P(1+mu)F(y)/q^b + sum h."""
    T = T_gen(b, q)
    mu_q, _ = mu_c(b, q)
    zy, zz = zpath(list(y), q), zpath(list(zeta), q)
    tau = lambda z, j: z[-1] if j == -1 else z[j - 1] - z[j]
    h = lambda A, B: P * abs(A - B) + mu * abs(B + P * A) - (P - mu) * abs(B) - P * (1 + mu) * abs(A)
    NA = [j for j in range(b) if y[j] == y[j + 1]]
    tot = Fr(0)
    bad = []
    for j in range(-1, b):
        A, B = tau(zy, j), tau(zz, j)
        hj = h(A, B)
        tot += hj
        # Lemma 3 bound
        if hj > 2 * mu * max(Fr(0), abs(B) - P * abs(A)):
            bad.append(('lemma3', j))
        if j in NA:
            if not hj < 2 * P * (1 + mu) * mu_q[j] * abs(zy[j]):
                bad.append(('NA term', j))
        elif hj > 0:
            bad.append(('nonNA term >0', j))
    Fy = l1(matvec(T, list(y)))
    lam = exact_lambda(T, list(y), list(zeta), P, mu)
    if lam / q ** b != P * (1 + mu) * Fy / q ** b + tot:
        bad.append('decomposition')
    return bad


def is_alt(y):
    return all(y[i] != y[i + 1] for i in range(len(y) - 1))


# ------------------------------------------------------------------ Part 1: vertex enumeration
def vertex_enum(b, Ps, mus, exact):
    n = b + 1
    Tf = T_gen(b, q)
    T = np.array([[float(v) for v in r] for r in Tf])
    D = d_formula(b, q)
    ys = [y for y in itertools.product([1, -1], repeat=n) if y[0] == 1]  # mod global sign
    pairs = []
    E = np.eye(n)
    for s in range(n + 1):
        for R in itertools.combinations(range(n), s):
            for I in itertools.combinations(range(n), n - s):
                Nm = np.vstack([T[list(R)], E[list(I)]]) if n > 0 else None
                if abs(np.linalg.det(Nm)) < 1e-9 * max(1.0, np.abs(Nm).max() ** n):
                    continue
                pairs.append((R, I, np.linalg.inv(Nm)))
    results = []
    for P in Ps:
        for y in ys:
            yv = np.array(y, float)
            Ty = T @ yv
            best = {mu: (-np.inf, None) for mu in mus}
            nvert = 0
            for (R, I, Ninv) in pairs:
                opts = [[0.0, Ty[r], -float(P) * Ty[r]] for r in R] + [[1.0, -1.0] for _ in I]
                rhs = np.array(list(itertools.product(*opts)), float)  # K x n
                Z = rhs @ Ninv.T
                ok = np.all(np.abs(Z) <= 1 + 1e-9, axis=1)
                Z = np.clip(Z[ok], -1, 1)
                if Z.shape[0] == 0:
                    continue
                nvert += Z.shape[0]
                F1 = np.abs((yv - Z) @ T.T).sum(1)
                F2 = np.abs((Z + float(P) * yv) @ T.T).sum(1)
                F3 = np.abs(Z @ T.T).sum(1)
                for mu in mus:
                    lam = float(P) * F1 + float(mu) * F2 - float(P - mu) * F3
                    k = int(np.argmax(lam))
                    if lam[k] > best[mu][0]:
                        best[mu] = (lam[k], (R, I, rhs[ok][k]))
            for mu in mus:
                bound = float(P * (1 + mu) * D)
                results.append((P, mu, y, best[mu][0] / bound, best[mu][1], nvert))
    return results, D


def exact_vertex(b, P, y, info):
    """Re-solve the vertex exactly with Fractions."""
    R, I, rhs_f = info
    n = b + 1
    T = T_gen(b, q)
    Ty = matvec(T, list(map(Fr, y)))
    rows, rhs = [], []
    for idx, r in enumerate(R):
        rows.append(list(T[r]))
        v = rhs_f[idx]
        cands = [Fr(0), Ty[r], -P * Ty[r]]
        rhs.append(min(cands, key=lambda c: abs(float(c) - v)))
    for idx, i in enumerate(I):
        rows.append([Fr(1) if j == i else Fr(0) for j in range(n)])
        rhs.append(Fr(int(round(rhs_f[len(R) + idx]))))
    # Gaussian elimination
    A = [row[:] + [rv] for row, rv in zip(rows, rhs)]
    for c in range(n):
        piv = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[piv] = A[piv], A[c]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c] / A[c][c]
                A[r] = [a - f * bb for a, bb in zip(A[r], A[c])]
    return [A[i][n] / A[i][i] for i in range(n)]


def part1():
    print('=== Part 1: full arrangement-vertex enumeration ===')
    fr_mu = [Fr(3, 5), Fr(1), Fr(random.randint(60, 100), 100)]
    for b in range(1, BMAX_VERTEX + 1):
        t0 = time.time()
        Ps = [Fr(4), Fr(6)] if b >= 6 else [Fr(4), Fr(6), Fr(random.randint(401, 1000), 100)]
        mus = fr_mu
        res, D = vertex_enum(b, Ps, mus, exact=False)
        worst_nonalt = max((r for r in res if not is_alt(r[2])), key=lambda r: r[3])
        worst_alt = max((r for r in res if is_alt(r[2])), key=lambda r: r[3])
        # exact re-check of worst non-alternating and the alternating one
        out = []
        for r in (worst_nonalt, worst_alt):
            P, mu, y, ratio, info, nv = r
            z = exact_vertex(b, P, y, info)
            assert all(abs(v) <= 1 for v in z)
            lam = exact_lambda(T_gen(b, q), list(map(Fr, y)), z, P, mu)
            bad = per_term_check(b, list(map(Fr, y)), z, P, mu)
            out.append((str(P), str(mu), y, float(lam / (P * (1 + mu) * D)), bad))
        # exact per-term check at every non-alternating y's best vertex, for P=4
        nbad = 0
        if b <= 5:
            for r in res:
                P, mu, y, ratio, info, nv = r
                z = exact_vertex(b, P, y, info)
                bad = per_term_check(b, list(map(Fr, y)), z, P, mu)
                lam = exact_lambda(T_gen(b, q), list(map(Fr, y)), z, P, mu)
                bnd = P * (1 + mu) * D
                if bad or lam > bnd or (not is_alt(y) and lam >= bnd):
                    nbad += 1
        print('b=%d  #(P,mu,y)=%d  vertices/(y,P)~%d  max ratio non-alt=%.6f  alt=%.6f  time=%.1fs'
              % (b, len(res), res[0][5], worst_nonalt[3], worst_alt[3], time.time() - t0))
        print('     exact recheck worst non-alt: P=%s mu=%s y=%s ratio=%.6f per-term-violations=%s'
              % out[0])
        print('     exact recheck alt          : P=%s mu=%s y=%s ratio=%.6f per-term-violations=%s'
              % out[1])
        if b <= 5:
            print('     exact recheck of all %d maximisers: violations=%d' % (len(res), nbad))
        sys.stdout.flush()


# ------------------------------------------------------------------ Part 2: random + line search
def part2():
    print('=== Part 2: random starts + exact 1-D piecewise-linear line search ===')
    for b in range(1, 7):
        t0 = time.time()
        n = b + 1
        Tq = T_gen(b, q)
        T = np.array([[float(v) for v in r] for r in Tq])
        D = float(d_formula(b, q))
        combos = [(4.0, 0.6), (4.0, 1.0), (6.0, 0.6), (6.0, 1.0)]
        for _ in range(4):
            combos.append((float(rng.uniform(4, 12)), float(rng.uniform(0.6, 1.0))))
        worst = (-1, None)
        worst_alt = (-1, None)
        S = 64
        for (P, mu) in combos:
            for y in itertools.product([1, -1], repeat=n):
                yv = np.array(y, float)

                def lam(Z):
                    return (P * np.abs((yv - Z) @ T.T).sum(-1) + mu * np.abs((Z + P * yv) @ T.T).sum(-1)
                            - (P - mu) * np.abs(Z @ T.T).sum(-1))
                Z = np.vstack([rng.uniform(-1, 1, (S // 2, n)),
                               rng.choice([-1.0, 1.0], (S // 4, n)),
                               rng.choice([-1.0, 0.0, 1.0], (S - S // 2 - S // 4, n))])
                cur = lam(Z)
                for it in range(40 * n):
                    kind = it % 3
                    if kind == 0:
                        d = np.zeros((S, n)); d[np.arange(S), rng.integers(0, n, S)] = 1.0
                    elif kind == 1:
                        d = rng.normal(size=(S, n))
                    else:
                        d = np.zeros((S, n)); i1 = rng.integers(0, n, S); i2 = rng.integers(0, n, S)
                        d[np.arange(S), i1] = 1.0; d[np.arange(S), i2] += rng.choice([-1.0, 1.0], S)
                    # feasible t-interval
                    with np.errstate(divide='ignore', invalid='ignore'):
                        lo = np.where(d > 0, (-1 - Z) / d, np.where(d < 0, (1 - Z) / d, -np.inf)).max(1)
                        hi = np.where(d > 0, (1 - Z) / d, np.where(d < 0, (-1 - Z) / d, np.inf)).min(1)
                        Td = d @ T.T
                        cands = [-(Z @ T.T) / Td, ((yv - Z) @ T.T) / Td, -((Z + P * yv) @ T.T) / Td]
                    C = np.concatenate(cands + [lo[:, None], hi[:, None], np.zeros((S, 1))], 1)
                    C = np.where(np.isfinite(C), C, 0.0)
                    C = np.clip(C, lo[:, None], hi[:, None])
                    Zc = Z[:, None, :] + C[:, :, None] * d[:, None, :]
                    Zc = np.clip(Zc, -1, 1)
                    L = lam(Zc)
                    k = L.argmax(1)
                    newv = L[np.arange(S), k]
                    upd = newv > cur + 1e-13
                    Z[upd] = Zc[np.arange(S), k][upd]
                    cur = np.maximum(cur, newv)
                    if it % (10 * n) == 10 * n - 1:  # perturb worst half
                        order = np.argsort(cur)
                        idx = order[: S // 4]
                        Z[idx] = np.clip(Z[order[-1]] + rng.normal(scale=0.3, size=(len(idx), n)), -1, 1)
                        cur[idx] = lam(Z[idx])
                kbest = int(cur.argmax())
                ratio = cur[kbest] / (P * (1 + mu) * D)
                rec = (ratio, (P, mu, y, Z[kbest].copy()))
                if is_alt(y):
                    worst_alt = max(worst_alt, rec, key=lambda r: r[0])
                else:
                    worst = max(worst, rec, key=lambda r: r[0])
        # exact re-evaluation of the worst non-alternating point (float -> exact Fraction)
        P, mu, y, z = worst[1]
        Pf, muf = Fr(P), Fr(mu)
        zf = [Fr(float(v)) for v in z]
        lamx = exact_lambda(Tq, list(map(Fr, y)), zf, Pf, muf)
        bad = per_term_check(b, list(map(Fr, y)), zf, Pf, muf)
        print('b=%d  max ratio non-alt=%.6f (exact %.6f, per-term violations %s)  alt=%.6f  time=%.1fs  worst y=%s P=%.3f mu=%.3f'
              % (b, worst[0], float(lamx / (Pf * (1 + muf) * d_formula(b, q))), bad, worst_alt[0],
                 time.time() - t0, y, P, mu))
        sys.stdout.flush()


if MODE in ('all', 'v'):
    part1()
if MODE in ('all', 'r'):
    part2()
