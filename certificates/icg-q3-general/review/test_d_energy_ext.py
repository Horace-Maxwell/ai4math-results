"""(d, extended) Same brute force as test_d_energy.py, chunked, for more orders; dense
eigvalsh for all sets at n=675 and the top sets elsewhere.  Eigenvalues lambda_t are exact
integers (Kluyver Ramanujan sums); the chunked sums are done in int64 (exact)."""
import sys, time
from math import gcd
import numpy as np
from rv_core import ramanujan, divisors, T_gen, d_formula

cases = [(5, 2, 3, 3, 'all'), (11, 2, 3, 1, 'all'), (7, 2, 3, 3, 40), (5, 2, 3, 5, 2), (5, 4, 3, 1, 25)]
allok = True
t_all = time.time()
for (p, a, q, b, ndense) in cases:
    t0 = time.time()
    n = p ** a * q ** b
    divs = [d for d in divisors(n) if d != n]
    K = len(divs)
    C = np.array([[ramanujan(n // d, t) for t in range(n)] for d in divs], dtype=np.int64)
    masks = np.arange(1, 1 << K, dtype=np.int64)
    E = np.empty(len(masks), dtype=np.int64)
    ch = max(1, (1 << 22) // n)
    for s in range(0, len(masks), ch):
        mm = masks[s:s + ch]
        S = ((mm[:, None] >> np.arange(K)[None, :]) & 1).astype(np.int64)
        E[s:s + ch] = np.abs(S @ C).sum(1)
    # FFT cross-check on all sets (float)
    gcds = np.array([gcd(v, n) for v in range(n)])
    Gidx = np.array([divs.index(g) if g in divs else -1 for g in gcds])  # g=n at v=0 -> -1
    fft_bad = 0
    for s in range(0, len(masks), ch):
        mm = masks[s:s + ch]
        S = ((mm[:, None] >> np.arange(K)[None, :]) & 1).astype(float)
        rows = np.where(Gidx[None, :] >= 0, S[:, np.maximum(Gidx, 0)], 0.0)
        ev = np.fft.fft(rows, axis=1)
        Ef = np.abs(ev.real).sum(1)
        fft_bad += int((np.abs(Ef - E[s:s + ch]) > 1e-6 * E[s:s + ch]).sum()) + int((np.abs(ev.imag).max(1) > 1e-6).sum())
    order = np.argsort(-E, kind='stable')
    Emax = int(E[order[0]])
    nmax = int((E == Emax).sum())
    best = sorted(divs[k] for k in range(K) if masks[order[0]] >> k & 1)
    Dstar = sorted(p ** i * q ** j for i in range(a + 1) for j in range(b + 1) if (i + j) % 2 == 0)
    formula = (n + d_formula(a, p) * d_formula(b, q)) / 2
    # dense eigvalsh on actual adjacency matrices
    idx = np.arange(n)
    G = np.gcd((idx[:, None] - idx[None, :]) % n, n)
    sel = range(len(masks)) if ndense == 'all' else order[:ndense]
    dense_bad = 0
    for kk in sel:
        D = [divs[k] for k in range(K) if masks[kk] >> k & 1]
        A = np.isin(G, D).astype(float)
        np.fill_diagonal(A, 0.0)
        Ed = np.abs(np.linalg.eigvalsh(A)).sum()
        if abs(Ed - E[kk]) > 1e-6 * E[kk]:
            dense_bad += 1
    ok = nmax == 1 and best == Dstar and Emax == formula and fft_bad == 0 and dense_bad == 0
    allok &= ok
    print('n=%d=%d^%d*%d^%d #sets=%d Emax=%d formula=%s #max=%d argmax==D*:%s 2nd=%d fft_bad=%d dense_bad=%d/%d %s %.1fs'
          % (n, p, a, q, b, len(masks), Emax, formula, nmax, best == Dstar, int(E[order[1]]), fft_bad,
             dense_bad, len(sel), 'OK' if ok else 'FAIL', time.time() - t0))
    sys.stdout.flush()
print('ALL OK:', allok, 'total %.1fs' % (time.time() - t_all))
