"""Referee-2: exact branch-and-bound over sign matrices, for fixed shape (a, b) and fixed parameters (p, q) (int or Fraction).

Enumerates columns from the right (c_b first).  Column-path identity (Paper 1 Lemma 4 applied to each row of MY, summed):
    G(Y) = sum_{j<b} Q q^j || M (q^{b-1-j} c_j - W_j) ||_1 + ||M W_{-1}||_1 - 2 ((M W_{-1})_a)^-,
    W_{b-1} = c_b,  W_{j-1} = W_j + Q q^{b-1-j} c_j        (W_j = q^{b-1-j} zeta_j).
Upper bound for the unexplored columns 0..j-1 (from the potential identity with s >= 0, i.e. Lemma S at these (p,q)):
    G <= acc + D_a Q sum_{j'<j} (q^{b-1} + q^{b-1-j'} nu_{j'-1}) + nu_{j-1} ||M W_{j-1}||_1,   nu_j = q^{j+1} mu_j.
Lemma S at the given (p, q) is verified first, exactly, in the crude form (|(M zeta)_i| <= ||row_i M||_1, cell bound of Lemma 6).
Every leaf with G >= threshold is re-evaluated with the matrix model Z = M Y N^T (r2core.G).
Returns (max G found >= threshold, list of all Y with G >= threshold, node count).
"""
import itertools, sys, time
from fractions import Fraction as Fr
from r2core import T, dd, de, G as Gmatrix, Theta, anti, trunc


def lemmaS_crude_ok(M, a, q):
    Q = q - 1
    vecs = list(itertools.product([1, -1], repeat=a + 1))
    rows = [sum(abs(x) for x in M[i]) for i in range(a + 1)]
    sa = tuple((-1) ** i for i in range(a + 1))
    Da = sum(abs(sum(M[i][k] * sa[k] for k in range(a + 1))) for i in range(a + 1))
    for c in vecs:
        A = [sum(M[i][k] * c[k] for k in range(a + 1)) for i in range(a + 1)]
        Dc = Da - sum(abs(x) for x in A)
        pen = sum(max(0, rows[i] - Q * abs(A[i])) for i in range(a + 1))
        # affine in mu in [0,1]: mu=0 gives Q*Dc >= 0 ; mu=1 gives 2*Q*Dc - 2*pen
        if Dc < 0 or 2 * Q * Dc - 2 * pen < 0:
            return False
        if c not in (sa, tuple(-x for x in sa)) and not (Dc > 0 and 2 * Q * Dc - 2 * pen > 0):
            return False
    return True


def bnb(a, b, p, q, threshold=None, verify_S=True):
    M = T(a, p)
    if all(x.denominator == 1 for row in M for x in row) and Fr(q).denominator == 1:
        M = [[int(x) for x in row] for row in M]
        q = int(q)
    Q = q - 1
    if verify_S:
        assert lemmaS_crude_ok(M, a, q), "Lemma S (crude) fails at these parameters: bound invalid"
    vecs = list(itertools.product([1, -1], repeat=a + 1))
    Mc = {c: [sum(M[i][k] * c[k] for k in range(a + 1)) for i in range(a + 1)] for c in vecs}
    sa = tuple((-1) ** i for i in range(a + 1))
    Da = sum(abs(x) for x in Mc[sa])
    nu = {-1: 1}
    for j in range(b + 1):
        nu[j] = Q * q ** j - nu[j - 1]
    C = [0] * (b + 1)
    for j in range(1, b + 1):
        C[j] = C[j - 1] + Da * Q * (q ** (b - 1) + q ** (b - 1 - (j - 1)) * nu[j - 2])
    th = Theta(a, b, p, q)
    if threshold is None:
        threshold = th
    found = []
    nodes = 0

    def l1M(W):
        return sum(abs(sum(M[i][k] * W[k] for k in range(a + 1))) for i in range(a + 1))

    def rec(j, W, acc, cols):
        # columns j+1..b chosen (cols[0] = c_b, ...); state W = W_j; choose c_j
        nonlocal nodes
        for c in vecs:
            nodes += 1
            inc = Q * q ** j * sum(abs(x) for x in
                                   [sum(M[i][k] * (q ** (b - 1 - j) * c[k] - W[k]) for k in range(a + 1)) for i in range(a + 1)])
            acc2 = acc + inc
            W2 = [W[k] + Q * q ** (b - 1 - j) * c[k] for k in range(a + 1)]
            if j == 0:
                MW = [sum(M[i][k] * W2[k] for k in range(a + 1)) for i in range(a + 1)]
                Gv = acc2 + sum(abs(x) for x in MW) - 2 * max(0, -MW[a])
                if Gv >= threshold:
                    colsY = [c] + cols[::-1]  # c_0 .. c_b ... careful: cols holds c_b, c_{b-1}, ..., c_1
                    found.append((Gv, colsY))
                continue
            ub = acc2 + C[j] + nu[j - 1] * l1M(W2)
            if ub >= threshold:
                rec(j - 1, W2, acc2, cols + [c])

    for cb in vecs:
        if cb[a] != -1:
            continue
        nodes += 1
        W = list(cb)
        ub = C[b] + nu[b - 1] * l1M(W)
        if b == 0:
            continue
        if ub >= threshold:
            rec(b - 1, W, 0, [cb])
    # convert and verify with the matrix model
    N = T(b, q)
    res = []
    for Gv, colsY in found:
        # colsY = [c_0, c_1, ..., c_b]? build properly: rec appends in order c_b, c_{b-1}, ..., c_1 then c_0 at the leaf
        cols = colsY
        Y = [[cols[j][i] for j in range(b + 1)] for i in range(a + 1)]
        Gm = Gmatrix(Y, M, N)
        assert Gm == Gv, ("column-path G != matrix G", a, b, p, q, Y, Gm, Gv)
        res.append((Gv, Y))
    return th, res, nodes


if __name__ == "__main__":
    a, b = int(sys.argv[1]), int(sys.argv[2])
    p, q = Fr(sys.argv[3]), Fr(sys.argv[4])
    t0 = time.time()
    th, res, nodes = bnb(a, b, p, q)
    print(a, b, p, q, th, [(g, Y) for g, Y in res], nodes, f"{time.time()-t0:.1f}s")
