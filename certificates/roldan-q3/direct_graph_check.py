"""End-to-end numerical check of the q=3 Roldan result on the actual graphs.

Independent of the Ramanujan-sum energy model: builds the adjacency matrix of
ICG(n, D) for n = 27 p^2 (vertices Z/n, i ~ j iff gcd(i-j, n) in D), computes
its eigenvalues with LAPACK (numpy.linalg.eigvalsh), and sums absolute values.
Checks, for every one of the 2047 nonempty proper-divisor sets D:
  * |E_numeric(D) - E_model(D)| is tiny, where E_model is the exact integer
    value of the weighted Ramanujan formula (computed here from scratch);
  * E(D) < E(D*) with D* = {1, p^2, 3p, 9, 9p^2, 27p}.
This is a floating-point diagnostic for small p, not part of the proof.
"""
import sys, json, time, hashlib
from math import gcd
from pathlib import Path
import numpy as np

def phi(m):
    r, k, x = m, 2, m
    while k * k <= x:
        if x % k == 0:
            while x % k == 0:
                x //= k
            r -= r // k
        k += 1
    if x > 1:
        r -= r // x
    return r

def ramanujan_pp(l, k, a):
    """c_{l^k}(u) for v_l(u) = a (a may exceed k)."""
    if k == 0:
        return 1
    if k <= a:
        return l ** k - l ** (k - 1)
    if k == a + 1:
        return -(l ** a)
    return 0

def run(p):
    q = 3
    n = p * p * q ** 3
    pairs = [(c, d) for c in range(3) for d in range(4) if (c, d) != (2, 3)]
    star = {(0, 0), (2, 0), (1, 1), (0, 2), (2, 2), (1, 3)}
    star_mask = sum(1 << j for j, cd in enumerate(pairs) if cd in star)
    assert star_mask == 1445
    # model energy (exact integers)
    def model(mask):
        tot = 0
        for a in range(3):
            for b in range(4):
                lam = 0
                for j, (c, d) in enumerate(pairs):
                    if mask >> j & 1:
                        lam += ramanujan_pp(p, 2 - c, a) * ramanujan_pp(q, 3 - d, b)
                tot += phi(p ** (2 - a)) * phi(q ** (3 - b)) * abs(lam)
        return tot
    # actual graph: circulant first row, gcd class of each shift
    g = np.array([gcd(s, n) for s in range(n)])
    idx = (np.arange(n)[None, :] - np.arange(n)[:, None]) % n
    G = g[idx]
    div_of = {p ** c * q ** d: j for j, (c, d) in enumerate(pairs)}
    cls = np.full(G.shape, -1, dtype=np.int64)
    for dv, j in div_of.items():
        cls[G == dv] = j
    E_star_model = model(star_mask)
    assert E_star_model == 266 * p * p - 404 * p + 202
    worst_err, best_other, best_mask = 0.0, -1.0, None
    E_star_num = None
    t0 = time.time()
    for mask in range(1, 2048):
        sel = np.array([(mask >> j) & 1 for j in range(11)] + [0], dtype=np.float64)
        M = sel[cls]  # cls == -1 picks the trailing 0 (diagonal, gcd = n)
        assert np.allclose(M, M.T)
        ev = np.linalg.eigvalsh(M)
        E_num = float(np.abs(ev).sum())
        E_mod = model(mask)
        worst_err = max(worst_err, abs(E_num - E_mod))
        if mask == star_mask:
            E_star_num = E_num
        elif E_mod > best_other:
            best_other, best_mask = E_mod, mask
    assert best_other < E_star_model
    return {
        "p": p, "n": n, "masks": 2047, "max_abs_numeric_minus_model": worst_err,
        "E_star_model": E_star_model, "E_star_numeric": E_star_num,
        "best_competitor_model": best_other, "best_competitor_mask": best_mask,
        "gap": E_star_model - best_other, "gap_lower_bound_24(p^2-2p+2)": 24 * (p * p - 2 * p + 2),
        "seconds": time.time() - t0,
    }

if __name__ == "__main__":
    ps = [int(a) for a in sys.argv[1:]] or [5]
    out = [run(p) for p in ps]
    for r in out:
        print(json.dumps(r))
    dest = Path(__file__).with_name("direct_graph_check_" + "_".join(map(str, ps)) + ".json")
    dest.write_text(json.dumps({"results": out,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}, indent=2))
