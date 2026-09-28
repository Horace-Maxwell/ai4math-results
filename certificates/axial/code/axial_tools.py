# Exact-arithmetic toolkit for small commutative (non-associative) algebras given by
# structure constants.  Written from scratch for the round-7 "axial" task; it shares no code
# with the scout's sympy scripts (work/round7/scouting/thin-algebra/calc/).
#
# Conventions: an algebra of dimension n over Q is a table T[i][j] = coordinate vector of
# e_i * e_j (tuple of n Fractions).  Vectors are tuples of Fractions.  All linear algebra is
# done by hand (fraction-exact Gaussian elimination); no floating point anywhere.
from fractions import Fraction as Q
from itertools import product

def vec(n, d):
    """vector from dict {index: value}"""
    return tuple(Q(d.get(i, 0)) for i in range(n))

def add(u, v): return tuple(x + y for x, y in zip(u, v))
def sub(u, v): return tuple(x - y for x, y in zip(u, v))
def scale(s, u): return tuple(Q(s) * x for x in u)
def is_zero(u): return all(x == 0 for x in u)

class Alg:
    def __init__(self, T, names=None):
        self.T = T
        self.n = len(T)
        self.names = names or [f"e{i}" for i in range(self.n)]
        n = self.n
        for i in range(n):
            for j in range(n):
                assert len(T[i][j]) == n
    def mul(self, u, v):
        n = self.n
        r = [Q(0)] * n
        for i in range(n):
            if u[i] == 0: continue
            for j in range(n):
                if v[j] == 0: continue
                c = u[i] * v[j]
                t = self.T[i][j]
                for k in range(n):
                    if t[k]: r[k] += c * t[k]
        return tuple(r)
    def basis(self):
        n = self.n
        return [tuple(Q(1) if k == i else Q(0) for k in range(n)) for i in range(n)]
    def ad(self, u):
        """matrix (list of rows) of v -> u*v in the standard basis: column j = u*e_j"""
        cols = [self.mul(u, e) for e in self.basis()]
        n = self.n
        return [[cols[j][i] for j in range(n)] for i in range(n)]
    def is_commutative(self):
        n = self.n
        return all(self.T[i][j] == self.T[j][i] for i in range(n) for j in range(n))
    def show(self, u):
        parts = []
        for x, nm in zip(u, self.names):
            if x != 0: parts.append(f"{x}*{nm}")
        return " + ".join(parts) if parts else "0"

# ---------- linear algebra over Q ----------
def rref(rows):
    """row-reduced echelon form; returns (R, pivots)"""
    M = [list(r) for r in rows]
    if not M: return [], []
    m, n = len(M), len(M[0])
    piv = []
    r = 0
    for c in range(n):
        p = None
        for i in range(r, m):
            if M[i][c] != 0:
                p = i; break
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][c]
        M[r] = [x * inv for x in M[r]]
        for i in range(m):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        piv.append(c)
        r += 1
        if r == m: break
    return M[:r], piv

def rank(vectors):
    if not vectors: return 0
    return len(rref(vectors)[0])

def span_basis(vectors):
    """canonical basis (RREF rows) of the span"""
    if not vectors: return []
    R, _ = rref(vectors)
    return [tuple(r) for r in R]

def in_span(v, vectors):
    return rank(list(vectors) + [v]) == rank(list(vectors))

def nullspace(M):
    """basis of {x : M x = 0}, M given as list of rows"""
    if not M: return []
    n = len(M[0])
    R, piv = rref(M)
    free = [c for c in range(n) if c not in piv]
    basis = []
    for f in free:
        x = [Q(0)] * n
        x[f] = Q(1)
        for row, pc in zip(R, piv):
            x[pc] = -row[f]
        basis.append(tuple(x))
    return basis

def solve_coords(v, basis_vecs):
    """coordinates of v in the (independent) list basis_vecs; None if not in span"""
    n = len(v); k = len(basis_vecs)
    # augmented system: sum_j c_j b_j = v  -> rows i: [b_0[i] ... b_{k-1}[i] | v[i]]
    rows = [[basis_vecs[j][i] for j in range(k)] + [v[i]] for i in range(n)]
    R, piv = rref(rows)
    if k in piv: return None
    c = [Q(0)] * k
    for row, pc in zip(R, piv):
        c[pc] = row[k]
    # verify
    w = tuple(sum((c[j] * basis_vecs[j][i] for j in range(k)), Q(0)) for i in range(n))
    assert w == tuple(v)
    return c

def matsub_scalar(M, lam):
    n = len(M)
    return [[M[i][j] - (lam if i == j else 0) for j in range(n)] for i in range(n)]

def matvec(M, v):
    return tuple(sum((M[i][j] * v[j] for j in range(len(v))), Q(0)) for i in range(len(M)))

def charpoly(M):
    """characteristic polynomial det(tI - M) via Faddeev-LeVerrier; coefficients high->low"""
    n = len(M)
    I = [[Q(1) if i == j else Q(0) for j in range(n)] for i in range(n)]
    def mm(A, B):
        return [[sum((A[i][k] * B[k][j] for k in range(n)), Q(0)) for j in range(n)] for i in range(n)]
    coeffs = [Q(1)]
    Mk = [row[:] for row in I]
    AM = None
    for k in range(1, n + 1):
        AM = mm(M, Mk)
        ck = -sum((AM[i][i] for i in range(n)), Q(0)) / k
        coeffs.append(ck)
        Mk = [[AM[i][j] + (ck if i == j else 0) for j in range(n)] for i in range(n)]
    return coeffs

def polyval(coeffs, t):
    r = Q(0)
    for c in coeffs: r = r * t + c
    return r

# ---------- axial notions ----------
def eigen_decomposition(A, s, F):
    """For the element s and the candidate eigenvalue set F (list of Fractions), return
    dict lam -> basis of A_lam(s) (only nonzero ones) and a flag 'diagonalizable with spectrum in F'."""
    M = A.ad(s)
    spaces = {}
    total = 0
    F = list(dict.fromkeys(Q(t) for t in F))   # de-duplicate
    for lam in F:
        ns = nullspace(matsub_scalar(M, Q(lam)))
        if ns:
            spaces[Q(lam)] = ns
            total += len(ns)
    return spaces, total == A.n

def spectrum_via_charpoly(A, s, F):
    """independent check: char poly of ad_s equals prod (t - lam)^{dim A_lam}"""
    cp = charpoly(A.ad(s))
    return cp

def realized_fusion(A, s, spaces):
    """minimal fusion rules realised by the eigenspace decomposition of s:
    returns dict (lam, mu) -> set of nu with nonzero nu-component in some product
    u*v, u in A_lam(s), v in A_mu(s) (basis vectors suffice by bilinearity)."""
    lams = list(spaces.keys())
    allvecs = []
    owner = []
    for lam in lams:
        for v in spaces[lam]:
            allvecs.append(v); owner.append(lam)
    law = {}
    for i, (li) in enumerate(lams):
        for lj in lams:
            occ = set()
            for u in spaces[li]:
                for v in spaces[lj]:
                    w = A.mul(u, v)
                    coords = solve_coords(w, allvecs)
                    assert coords is not None
                    # group components by eigenvalue
                    for lam in lams:
                        comp = [coords[k] for k in range(len(allvecs)) if owner[k] == lam]
                        if any(x != 0 for x in comp): occ.add(lam)
            law[(li, lj)] = occ
    return law

def check_fusion(A, s, spaces, star):
    """check A_lam A_mu subset A_{lam*mu} for all lam, mu with nonzero eigenspaces.
    star: function (lam, mu) -> set of Fractions."""
    real = realized_fusion(A, s, spaces)
    ok = True
    bad = []
    for (l, m), occ in real.items():
        allowed = star(l, m)
        if not occ <= allowed:
            ok = False; bad.append((l, m, occ, allowed))
    return ok, bad, real

def subalgebra_generated(A, gens):
    """basis of the smallest subspace containing gens and closed under multiplication"""
    B = span_basis(list(gens))
    while True:
        new = list(B)
        for u in B:
            for v in B:
                new.append(A.mul(u, v))
        B2 = span_basis(new)
        if len(B2) == len(B): return B
        B = B2

def ideal_generated(A, gens):
    """basis of the smallest ideal containing gens (closure under multiplication by basis)"""
    B = span_basis(list(gens))
    E = A.basis()
    while True:
        new = list(B)
        for u in B:
            for e in E:
                new.append(A.mul(e, u)); new.append(A.mul(u, e))
        B2 = span_basis(new)
        if len(B2) == len(B): return B
        B = B2

def is_ideal(A, basisI):
    for u in basisI:
        for e in A.basis():
            if not in_span(A.mul(e, u), basisI) or not in_span(A.mul(u, e), basisI):
                return False
    return True

def same_space(U, W):
    return rank(list(U)) == rank(list(W)) == rank(list(U) + list(W))

def frobenius_forms(A):
    """basis of the space of bilinear forms G (n x n matrices, unknowns g_ij) with
    G(uv, w) = G(u, vw) for all basis u, v, w.  Returns list of matrices."""
    n = A.n
    E = A.basis()
    nvar = n * n
    rows = []
    for i in range(n):
        for j in range(n):
            for k in range(n):
                uv = A.mul(E[i], E[j])   # (e_i e_j, e_k) - (e_i, e_j e_k) = 0
                vw = A.mul(E[j], E[k])
                row = [Q(0)] * nvar
                for p in range(n):
                    row[p * n + k] += uv[p]       # sum_p uv_p g_{p k}
                    row[i * n + p] -= vw[p]       # sum_p vw_p g_{i p}
                rows.append(row)
    ns = nullspace(rows)
    return [[[x[p * n + q] for q in range(n)] for p in range(n)] for x in ns]
