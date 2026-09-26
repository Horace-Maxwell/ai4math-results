"""Fast exact integer enumeration of Z = T_a(p) Y T_b(q)^T over all sign matrices Y (numpy int64 / object for safety).
Integer p, q only (entries of T are integers). Returns arrays for hypothesis testing.
"""
import numpy as np
import itertools
from fractions import Fraction as Fr
from core import T, dfun, delta_last

def Tint(k, x):
    M = T(k, x)
    return np.array([[int(v) for v in row] for row in M], dtype=np.int64)

def all_Y(a, b, fix_corner=None):
    nc = (a + 1) * (b + 1)
    idx = np.arange(1 << nc, dtype=np.int64)
    Y = ((idx[:, None] >> np.arange(nc)) & 1) * 2 - 1      # (N, nc), row-major cells (i,j) -> i*(b+1)+j
    if fix_corner is not None:
        Y = Y[Y[:, nc - 1] == fix_corner]
    return Y.reshape(-1, a + 1, b + 1)

def Zall(Y, p, q):
    a = Y.shape[1] - 1; b = Y.shape[2] - 1
    M = Tint(a, p); N = Tint(b, q)
    # bound check
    assert (np.abs(M).sum() * np.abs(N).sum()) < 2**62
    return np.einsum('ui,nij,vj->nuv', M, Y, N)

def target(a, b, p, q):
    return int(dfun(a, p) * dfun(b, q) - 2 * delta_last(a, p) * delta_last(b, q))
