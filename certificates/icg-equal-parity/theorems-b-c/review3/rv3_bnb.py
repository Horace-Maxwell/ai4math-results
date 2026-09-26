"""Referee-3 exact branch and bound for max G(Y) over sign matrices Y of shape (a+1) x (b+1) with y_ab = -1, at one point
(p, q) (integers or rationals), written independently of review2/bnb.py.

G(Y) = sum_{(i,j) != (a,b)} |Z_ij| + Z_ab,  Z = T_a(p) Y T_b(q)^T   (eq. (2) of Paper 1; 2E - n for a divisor set).

Columns are fixed from the right (c_b first).  With W_{b-1} = c_b and W_{j-1} = W_j + P x^{b-1-j} c_j (x = q, P = q - 1),
Lemma 7 applied to every row of M Y gives the exact identity
    G = sum_{j<b} P x^j || M (x^{b-1-j} c_j - W_j) ||_1 + || M W_{-1} ||_1 - 2 ((M W_{-1})_a)^-.
Upper bound at a node where c_j0, ..., c_b are fixed (Lemma 18 summed over the rows, and psi >= 0):
    G <= acc + x^b [ d_a(p) sum_{j<j0} chat_j + mu_{j0-1} x^{-(b-j0)} || M W_{j0-1} ||_1 ],
where chat_j = P(1 + mu_{j-1})/x.  psi >= 0 is checked exactly at the given (p, q) first (crude form of Lemma 22 at mu = 0
and mu = 1, including omega_i <= P|alpha_i| for the alternating columns); if it fails the run aborts.
Every leaf with G >= threshold is recomputed from the matrix model Z = M Y N^T; the program reports all of them.
"""
import itertools, sys, time
from fractions import Fraction as Fr


def T(k, x):
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


def G_matrix(Y, M, N):
    a, b = len(Y) - 1, len(Y[0]) - 1
    MY = [[sum(M[i][k] * Y[k][j] for k in range(a + 1)) for j in range(b + 1)] for i in range(a + 1)]
    Z = [[sum(MY[i][j] * N[v][j] for j in range(b + 1)) for v in range(b + 1)] for i in range(a + 1)]
    return sum(abs(Z[i][v]) for i in range(a + 1) for v in range(b + 1)) - abs(Z[a][b]) + Z[a][b]


def dk(k, x):
    M = T(k, x)
    s = [(-1) ** i for i in range(k + 1)]
    v = [sum(M[i][j] * s[j] for j in range(k + 1)) for i in range(k + 1)]
    return sum(abs(z) for z in v), v[k]


def bnb(a, b, p, q, threshold=None):
    p, q = Fr(p), Fr(q)
    M = T(a, p)
    N = T(b, q)
    x, P = q, q - 1
    vecs = list(itertools.product([1, -1], repeat=a + 1))
    Mc = {c: [sum(M[i][k] * c[k] for k in range(a + 1)) for i in range(a + 1)] for c in vecs}
    sa = tuple((-1) ** i for i in range(a + 1))
    Da, dela = dk(a, p)
    Db, delb = dk(b, q)
    Theta = Da * Db - 2 * dela * delb
    thr = Theta if threshold is None else threshold
    # psi >= 0 on the cube (crude Lemma 22 at mu in {0, 1}), exactly at this point
    omega = [sum(abs(z) for z in M[i]) for i in range(a + 1)]
    for c in vecs:
        Dc = Da - sum(abs(z) for z in Mc[c])
        pen = sum(max(Fr(0), omega[i] - P * abs(Mc[c][i])) for i in range(a + 1))
        if Dc < 0 or P * Dc < 0 or 2 * P * Dc - 2 * pen < 0:
            raise RuntimeError(f'psi >= 0 not certified at p={p}, q={q}, c={c}')
    mu = {-1: Fr(1)}
    for j in range(b + 1):
        mu[j] = (P - mu[j - 1]) / x
    chat = [P * (1 + mu[j - 1]) / x for j in range(b + 1)]
    pref = [Fr(0)]
    for j in range(b + 1):
        pref.append(pref[-1] + chat[j])          # pref[j0] = sum_{j<j0} chat_j
    xb = x ** b
    found = []
    nodes = [0]

    def l1(v):
        return sum(abs(z) for z in v)

    def MW(W):
        return [sum(M[i][k] * W[k] for k in range(a + 1)) for i in range(a + 1)]

    def rec(j, W, acc, cols):
        # columns j+1..b fixed; W = W_j; choose c_j
        for c in vecs:
            nodes[0] += 1
            xp = x ** (b - 1 - j)
            inc = P * x ** j * l1([sum(M[i][k] * (xp * c[k] - W[k]) for k in range(a + 1)) for i in range(a + 1)])
            W2 = [W[k] + P * xp * c[k] for k in range(a + 1)]
            acc2 = acc + inc
            if j == 0:
                mw = MW(W2)
                Gv = acc2 + l1(mw) - 2 * max(Fr(0), -mw[a])
                if Gv >= thr:
                    found.append((Gv, [c] + cols))
                continue
            ub = acc2 + xb * (Da * pref[j] + mu[j - 1] * l1(MW(W2)) / x ** (b - j))
            if ub >= thr:
                rec(j - 1, W2, acc2, [c] + cols)

    for cb in vecs:
        if cb[a] != -1:
            continue
        nodes[0] += 1
        W = [Fr(z) for z in cb]
        ub = xb * (Da * pref[b] + mu[b - 1] * l1(MW(W)))
        if ub >= thr:
            rec(b - 1, W, Fr(0), [cb])
    res = []
    for Gv, cols in found:
        Y = [[cols[j][i] for j in range(b + 1)] for i in range(a + 1)]
        Gm = G_matrix(Y, M, N)
        assert Gm == Gv, ('path identity != matrix model', a, b, p, q)
        res.append((Gm, Y))
    return Theta, res, nodes[0]


def extremal(a, b):
    Ym = [[-(-1) ** (i + j) for j in range(b + 1)] for i in range(a + 1)]
    Yp = [[(-1) ** (i + j) for j in range(b + 1)] for i in range(a + 1)]
    Yp[a][b] = -1
    return Ym, Yp


if __name__ == '__main__':
    runs = []
    for arg in sys.argv[1:]:
        sh, pt = arg.split('@')
        a_, b_ = map(int, sh.split(','))
        p_, q_ = map(Fr, pt.split(','))
        runs.append((a_, b_, p_, q_))
    nfail = 0
    for a_, b_, p_, q_ in runs:
        t0 = time.time()
        Th, res, nodes = bnb(a_, b_, p_, q_)
        Ym, Yp = extremal(a_, b_)
        ok = sorted(map(str, [Y for _, Y in res])) == sorted(map(str, [Ym, Yp])) and all(g == Th for g, _ in res)
        nfail += not ok
        print(f'({a_},{b_}) p={p_} q={q_}: Theta={Th}; matrices with G >= Theta: {len(res)} '
              f'{"= exactly Y-, Y+ with G = Theta: OK" if ok else "UNEXPECTED: " + str(res)[:300]}; nodes={nodes}; '
              f'{time.time() - t0:.1f}s', flush=True)
    print(f'runs {len(runs)}, failures {nfail}')
