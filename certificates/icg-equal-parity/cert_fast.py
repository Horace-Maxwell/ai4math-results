"""Vectorised version of cert22.py (same certificate, exact int64 coefficient arithmetic with overflow guard).

For a shape (a,b) and region p = p0 + s, q = q0 + t (s,t >= 0):
  every entry Z_uv(Y) is a polynomial with coefficient array C[u,v] of shape (a+1, b+1) (bidegree <= (a,b)).
  For each Y (Y_ab = -1): determined entries (all coefficients >= 0, or all <= 0) get their sign; undetermined entries are bounded
  coefficientwise by |coefficients| (sufficient); Y's failing this sufficient test are re-checked exactly by branching (as cert22.py).
Certificate: for every Y and every admissible sign pattern S (S_ab=+1), target - <S, Z(Y)> has all coefficients >= 0 and a positive
constant term, except for the two conjectured maximisers where it vanishes identically for their optimal S.
Usage: python3 cert_fast.py a b p0 q0 [chunk_log2]
"""
import sys, itertools, time
import numpy as np
import cert22

def poly_to_arr(P, a, b):
    A = np.zeros((a + 1, b + 1), dtype=np.int64)
    for (i, j), v in P.items():
        assert i <= a and j <= b, (i, j)
        A[i, j] = v
    return A

def main(a, b, p0, q0, chunk_log2=14):
    t0 = time.time()
    Pp = cert22.lin_s(p0); Qq = cert22.lin_t(q0)
    M = cert22.Tpoly(a, Pp); N = cert22.Tpoly(b, Qq)
    cells = [(i, j) for i in range(a + 1) for j in range(b + 1)]
    nc = len(cells); corner = nc - 1
    # K[c_out, c_in, :, :]  (c_out = (u,v), c_in = (i,j)) coefficient arrays of M_ui N_vj
    K = np.zeros((nc, nc, a + 1, b + 1), dtype=np.int64)
    maxabs = 0
    for co, (u, v) in enumerate(cells):
        for ci, (i, j) in enumerate(cells):
            arr = poly_to_arr(cert22.pmul(M[u][i], N[v][j]), a, b)
            K[co, ci] = arr
            maxabs = max(maxabs, int(np.abs(arr).max()))
    # target polynomial
    def dpol(k, X):
        R = cert22.pmul(cert22.const(2 * k + 1), cert22.ppow(X, k))
        for j in range(k):
            R = cert22.padd(R, cert22.pmul(cert22.const(4 * (-1) ** (k - j) * (j + 1)), cert22.ppow(X, j)))
        return R
    def delpol(k, X):
        R = cert22.ppow(X, k)
        for i in range(k):
            R = cert22.padd(R, cert22.pmul(cert22.const(2 * (-1) ** (k - i)), cert22.ppow(X, i)))
        return R
    tgt = poly_to_arr(cert22.padd(cert22.pmul(dpol(a, Pp), dpol(b, Qq)), cert22.pmul(cert22.const(2), cert22.pmul(delpol(a, Pp), delpol(b, Qq))), -1), a, b)
    # overflow guard: |sum| <= nc * nc * maxabs + |tgt|
    bound = nc * nc * maxabs + int(np.abs(tgt).max())
    assert bound < 2 ** 62, "int64 overflow risk"
    Kf = K.reshape(nc, nc, -1)            # (out, in, coef)
    free = nc - 1
    total = 1 << free
    chunk = 1 << min(chunk_log2, free)
    anti = tuple(-(-1) ** (i + j) for (i, j) in cells)
    trunc = tuple([(-1) ** (i + j) for (i, j) in cells][:-1] + [-1])
    n_fallback = 0; n_tight = 0; tight = []; failures = []
    for start in range(0, total, chunk):
        idx = np.arange(start, min(total, start + chunk), dtype=np.int64)
        Yf = ((idx[:, None] >> np.arange(free)) & 1) * 2 - 1
        Y = np.concatenate([Yf, -np.ones((len(idx), 1), dtype=np.int64)], axis=1)   # (B, nc)
        Z = np.einsum('bi,oic->boc', Y, Kf)                                             # (B, nc_out, coef)
        pos = (Z >= 0).all(axis=2); neg = (Z <= 0).all(axis=2)
        sign = np.where(pos, 1, np.where(neg, -1, 0))                                   # 0 = undetermined
        sign[:, corner] = 1                                                             # corner enters with +1
        undet = (sign == 0)
        val = np.einsum('bo,boc->bc', sign, Z)                                          # determined part (+corner)
        slackbound = np.einsum('bo,boc->bc', undet.astype(np.int64), np.abs(Z))         # |coef| bound for undetermined
        gap = tgt.reshape(1, -1) - val - slackbound
        ok = (gap >= 0).all(axis=1) & (gap[:, 0] > 0)
        bad_idx = np.nonzero(~ok)[0]
        for bi in bad_idx:
            y = tuple(int(v) for v in Y[bi])
            # exact fallback: branch over undetermined entries
            und = [o for o in range(nc) if undet[bi, o]]
            base = tgt - np.einsum('o,oc->c', sign[bi] * (~undet[bi]), Z[bi]).reshape(a + 1, b + 1)
            any_bad = False
            for sb in itertools.product([1, -1], repeat=len(und)):
                g = base.copy().reshape(-1)
                for o, s_ in zip(und, sb):
                    g = g - s_ * Z[bi, o]
                if not g.any():
                    n_tight += 1; tight.append(y); continue
                if (g < 0).any() or g[0] <= 0:
                    any_bad = True; failures.append((y, und, sb, g.tolist()))
            n_fallback += 1
    ok_tight = sorted(set(tight)) == sorted({anti, trunc})
    print(f"shape ({a},{b}) region p>={p0}, q>={q0}: #Y={total} fallback={n_fallback} #not-certified={len(failures)} "
          f"#tight={n_tight} tight_set_ok={ok_tight} time={time.time()-t0:.1f}s")
    for f in failures[:10]:
        print("  FAIL", f)
    return len(failures) == 0 and ok_tight

if __name__ == "__main__":
    a, b, p0, q0 = map(int, sys.argv[1:5])
    cl = int(sys.argv[5]) if len(sys.argv) > 5 else 14
    main(a, b, p0, q0, cl)
