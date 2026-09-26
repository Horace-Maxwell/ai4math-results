"""Exact polynomial certificate attempt for a fixed shape (a,b), all real p >= p0, q >= q0.

G(Y) = max_{S in {+-1}, S_ab=+1} <S, Z(Y)>, Z = T_a(p) Y T_b(q)^T.  Claim: target(p,q) - <S,Z(Y)> >= 0 for all S, Y (Y_ab=-1),
with equality (identically) only for the two conjectured maximisers paired with their sign pattern.
Method: polynomials in (s,t) with p = p0 + s, q = q0 + t (s,t >= 0); a polynomial with all coefficients >= 0 is >= 0 on the region.
To avoid 2^{2N} pairs we use, for each Y, the sign of each off-corner entry Z_uv(Y) when it is determined by its coefficients
(all >= 0 or all <= 0); only undetermined entries are branched over.
"""
import itertools, sys
from fractions import Fraction as Fr
from collections import defaultdict

def padd(A, B, c=1):
    C = defaultdict(int, A)
    for k, v in B.items():
        C[k] += c * v
    return {k: v for k, v in C.items() if v != 0}

def pmul(A, B):
    C = defaultdict(int)
    for (i, j), v in A.items():
        for (k, l), w in B.items():
            C[(i + k, j + l)] += v * w
    return {k: v for k, v in C.items() if v != 0}

def const(c): return {(0, 0): c} if c else {}

def lin_s(p0): return {(0, 0): p0, (1, 0): 1}   # p = p0 + s
def lin_t(q0): return {(0, 0): q0, (0, 1): 1}   # q = q0 + t

def ppow(A, e):
    R = const(1)
    for _ in range(e): R = pmul(R, A)
    return R

def Tpoly(k, X):
    """T_k(x) with x given as a polynomial X."""
    one = const(1); xm1 = padd(X, one, -1)
    M = [[None] * (k + 1) for _ in range(k + 1)]
    for i in range(k + 1):
        for j in range(k + 1):
            if i < k and j < k:
                if i + j <= k - 2: v = {}
                elif i + j == k - 1: v = padd({}, pmul(ppow(X, k - 1), xm1), -1)
                else: v = pmul(ppow(X, 2 * k - i - j - 2), pmul(xm1, xm1))
            elif i == k and j == k: v = one
            else:
                t = i if i < k else j
                v = pmul(ppow(X, k - t - 1), xm1)
            M[i][j] = v
    return M

def sign_of(P):
    if not P: return 0
    vals = list(P.values())
    if all(v >= 0 for v in vals): return 1
    if all(v <= 0 for v in vals): return -1
    return None

def run(a, b, p0, q0):
    Pp = lin_s(p0); Qq = lin_t(q0)
    M = Tpoly(a, Pp); N = Tpoly(b, Qq)
    # K[(u,v)][(i,j)] = M_ui N_vj
    K = {(u, v): {(i, j): pmul(M[u][i], N[v][j]) for i in range(a + 1) for j in range(b + 1)} for u in range(a + 1) for v in range(b + 1)}
    # target = d_a(p) d_b(q) - 2 delta_a(p) delta_b(q), computed as polynomials via checkerboard: d = sum |T s| ; use exact closed forms
    def dpol(k, X):
        R = pmul(const(2 * k + 1), ppow(X, k))
        for j in range(k):
            R = padd(R, pmul(const(4 * (-1) ** (k - j) * (j + 1)), ppow(X, j)))
        return R
    # delta_k(x) = (x^k (x-1) + 2(-1)^k)/(x+1): polynomial division; compute via sum_{t} of coefficients
    def delpol(k, X, x0):
        # delta_k(x) = x^k - 2x^{k-1} + 2x^{k-2} - ... + (-1)^{k} 2 ... use recursion delta_{k}= x delta_{k-1} ... compute numerically then fit:
        # closed form: delta_k(x) = sum_{i=0}^{k} c_i x^i with c_k=1, c_i = 2(-1)^{k-i} for i<k  (check: (x+1)*that = x^{k+1}-x^k+2(-1)^k)
        R = ppow(X, k)
        for i in range(k):
            R = padd(R, pmul(const(2 * (-1) ** (k - i)), ppow(X, i)))
        return R
    tgt = padd(pmul(dpol(a, Pp), dpol(b, Qq)), pmul(const(2), pmul(delpol(a, Pp, p0), delpol(b, Qq, q0))), -1)
    tgt = padd(tgt, const(1), -1)  # NEGATIVE CONTROL: target lowered by 1
    cells = [(i, j) for i in range(a + 1) for j in range(b + 1)]
    corner = (a, b)
    anti = {(i, j): -(-1) ** (i + j) for (i, j) in cells}
    trunc = {(i, j): (-1) ** (i + j) for (i, j) in cells}; trunc[corner] = -1
    nY = 0; nbranch = 0; bad = []; eq_found = []
    free = [c for c in cells if c != corner]
    for bits in itertools.product([1, -1], repeat=len(free)):
        Y = dict(zip(free, bits)); Y[corner] = -1
        Z = {}
        for c in cells:
            acc = {}
            for (i, j), s in Y.items():
                acc = padd(acc, K[c][(i, j)], s)
            Z[c] = acc
        # corner enters with + sign (S_ab = +1)
        base = Z[corner]
        undecided = []
        det = {}
        for c in cells:
            if c == corner: continue
            sg = sign_of(Z[c])
            if sg is None: undecided.append(c)
            else: det[c] = sg if sg != 0 else 1
        nY += 1
        for sb in itertools.product([1, -1], repeat=len(undecided)):
            nbranch += 1
            val = dict(base)
            for c, sg in det.items(): val = padd(val, Z[c], sg)
            for c, sg in zip(undecided, sb): val = padd(val, Z[c], sg)
            gap = padd(tgt, val, -1)
            if not gap:
                eq_found.append(tuple(Y[c] for c in cells))
                continue
            if any(v < 0 for v in gap.values()) or gap.get((0, 0), 0) <= 0:
                bad.append((tuple(Y[c] for c in cells), undecided, sb, gap))
    return nY, nbranch, bad, eq_found, anti, trunc, cells

if __name__ == "__main__":
    a, b, p0, q0 = map(int, sys.argv[1:5])
    nY, nbranch, bad, eq, anti, trunc, cells = run(a, b, p0, q0)
    print(f"shape ({a},{b}) region p>={p0}, q>={q0}: #Y={nY} #branches={nbranch} #not-certified={len(bad)} #identically-tight={len(eq)}")
    print("tight Y:", sorted(set(eq)) == sorted({tuple(anti[c] for c in cells), tuple(trunc[c] for c in cells)}), sorted(set(eq)))
    for Y, und, sb, gap in bad[:12]:
        print("  not certified:", Y, "undecided", und, "branch", sb, "gap poly", dict(sorted(gap.items())))
