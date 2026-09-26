"""Referee-2: tiny exact arithmetic for rational functions on the two parameter regions (independent of sympy / the authors'
sign_on).

Region 'big':  P = 4 + s, Q = 2 + t   (s, t >= 0)      [p >= 5, q >= 3]
Region 'p3' :  P = 2,     Q = 4 + t   (t >= 0)         [p = 3,  q >= 5]

Every quantity used by the certificates is  num(s,t) / (q^K (q+1)^L)  with num an integer polynomial, q = Q + 1 and
q + 1 = Q + 2; the denominator is positive on the region.  An element is stored as (num, K, L), num = {(i, j): int}.
Sign test ("certified sign"): +1 if all coefficients of num are >= 0 and the constant term is > 0; -1 symmetrically;
0 if num is identically zero; None otherwise.  (Sound: for s, t >= 0 such a polynomial is > 0.)
"""
from fractions import Fraction as Fr


def padd(a, b, sign=1):
    r = dict(a)
    for k, v in b.items():
        r[k] = r.get(k, 0) + sign * v
        if r[k] == 0:
            del r[k]
    return r


def pmul(a, b):
    r = {}
    for (i1, j1), v1 in a.items():
        for (i2, j2), v2 in b.items():
            k = (i1 + i2, j1 + j2)
            r[k] = r.get(k, 0) + v1 * v2
    return {k: v for k, v in r.items() if v != 0}


def pscal(a, c):
    return {k: v * c for k, v in a.items() if v * c != 0} if c != 0 else {}


def ppow(a, n):
    r = {(0, 0): 1}
    for _ in range(n):
        r = pmul(r, a)
    return r


class Region:
    # name -> (P0, P free?, Q0): P = P0 + s (or P = P0 if fixed), Q = Q0 + t.  'big', 'p3' are the regions of the claim;
    # the others are used ONLY as negative controls (enlarged regions).
    SPEC = {'big': (4, True, 2), 'p3': (2, False, 4),
            'nc_P3': (3, True, 2), 'nc_Q1': (4, True, 1), 'nc_p3Q3': (2, False, 3), 'nc_P2Q2': (2, False, 2)}

    def __init__(self, name):
        self.name = name
        P0, Pfree, Q0 = self.SPEC[name]
        self.P0, self.Pfree, self.Q0 = P0, Pfree, Q0
        self.P = {(0, 0): P0, (1, 0): 1} if Pfree else {(0, 0): P0}
        self.Q = {(0, 0): Q0, (0, 1): 1}
        self.q = padd(self.Q, {(0, 0): 1})
        self.q1 = padd(self.Q, {(0, 0): 2})
        self._qp = {0: {(0, 0): 1}}
        self._q1p = {0: {(0, 0): 1}}

    def qpow(self, n):
        if n not in self._qp:
            self._qp[n] = pmul(self.qpow(n - 1), self.q)
        return self._qp[n]

    def q1pow(self, n):
        if n not in self._q1p:
            self._q1p[n] = pmul(self.q1pow(n - 1), self.q1)
        return self._q1p[n]

    # constructors
    def const(self, c):
        return RF(self, {(0, 0): c} if c != 0 else {}, 0, 0)

    def poly(self, num):
        return RF(self, num, 0, 0)

    def PP(self):
        return RF(self, self.P, 0, 0)

    def QQ(self):
        return RF(self, self.Q, 0, 0)


class RF:
    __slots__ = ('R', 'num', 'K', 'L')

    def __init__(self, R, num, K, L):
        self.R, self.num, self.K, self.L = R, num, K, L

    def _lift(self, K, L):
        n = self.num
        if K > self.K:
            n = pmul(n, self.R.qpow(K - self.K))
        if L > self.L:
            n = pmul(n, self.R.q1pow(L - self.L))
        return n

    def __add__(self, o):
        if not isinstance(o, RF):
            o = self.R.const(o)
        K, L = max(self.K, o.K), max(self.L, o.L)
        return RF(self.R, padd(self._lift(K, L), o._lift(K, L)), K, L)

    __radd__ = __add__

    def __neg__(self):
        return RF(self.R, pscal(self.num, -1), self.K, self.L)

    def __sub__(self, o):
        if not isinstance(o, RF):
            o = self.R.const(o)
        return self + (-o)

    def __rsub__(self, o):
        return (-self) + o

    def __mul__(self, o):
        if not isinstance(o, RF):
            return RF(self.R, pscal(self.num, o), self.K, self.L)
        return RF(self.R, pmul(self.num, o.num), self.K + o.K, self.L + o.L)

    __rmul__ = __mul__

    def div_q(self, n=1):
        return RF(self.R, self.num, self.K + n, self.L)

    def div_q1(self, n=1):
        return RF(self.R, self.num, self.K, self.L + n)

    def sign(self):
        if not self.num:
            return 0
        vals = list(self.num.values())
        c0 = self.num.get((0, 0), 0)
        if c0 > 0 and all(v >= 0 for v in vals):
            return 1
        if c0 < 0 and all(v <= 0 for v in vals):
            return -1
        return None

    def evalf(self, s, t):
        """exact value at a point (Fractions), for grid sanity checks."""
        s, t = Fr(s), Fr(t)
        n = sum(v * s ** i * t ** j for (i, j), v in self.num.items())
        qv = Fr(self.R.Q0 + 1) + t
        return n / (qv ** self.K * (qv + 1) ** self.L)

    def absval(self):
        sg = self.sign()
        if sg is None:
            raise RuntimeError("undetermined sign in absval")
        return self if sg >= 0 else -self


def T_region(R, k):
    """T_k(p) with p = P + 1 as a matrix of RF (polynomials)."""
    p = padd(R.P, {(0, 0): 1})
    Pm1 = R.P  # p - 1
    n = k + 1
    Mx = [[None] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i == k and j == k:
                v = {(0, 0): 1}
            elif i == k or j == k:
                e = k - min(i, j)
                v = pmul(ppow(p, e - 1), Pm1)
            elif i + j <= k - 2:
                v = {}
            elif i + j == k - 1:
                v = pscal(pmul(ppow(p, k - 1), Pm1), -1)
            else:
                v = pmul(ppow(p, 2 * k - i - j - 2), pmul(Pm1, Pm1))
            Mx[i][j] = R.poly(v)
    return Mx
