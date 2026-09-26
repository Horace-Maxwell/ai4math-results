"""(d) Brute-force maximal energy of ICG_n(D) over all nonempty sets D of proper divisors.
Primary: exact integer eigenvalues lambda_t = sum_{d in D} c_{n/d}(t), t in Z/n (Kluyver formula).
Cross-checks: numpy FFT of the adjacency first row (all sets); dense eigvalsh of the actual
adjacency matrix (all sets for n=75,147; top sets for n=675,1875); JY matrix model ||T X T^T||_1."""
import sys, time
from math import gcd
import numpy as np
from rv_core import ramanujan, divisors, T_gen, d_formula

t_all = time.time()
cases = [(5, 2, 3, 1), (7, 2, 3, 1), (5, 2, 3, 3), (5, 4, 3, 1)]  # p, a=2r, q, b=2s+1
allok = True
for (p, a, q, b) in cases:
    t0 = time.time()
    n = p ** a * q ** b
    divs = [d for d in divisors(n) if d != n]
    K = len(divs)
    # exact Ramanujan table
    C = np.array([[ramanujan(n // d, t) for t in range(n)] for d in divs], dtype=np.int64)
    # exponents of each divisor
    def expo(d):
        i = j = 0
        while d % p == 0:
            d //= p; i += 1
        while d % q == 0:
            d //= q; j += 1
        return i, j
    ex = [expo(d) for d in divs]
    M = np.array(T_gen(a, p), dtype=object).astype(np.int64)
    N = np.array(T_gen(b, q), dtype=object).astype(np.int64)
    gcds = np.array([gcd(v, n) for v in range(n)])
    energies = {}
    model_mismatch = fft_mismatch = 0
    for mask in range(1, 1 << K):
        D = [divs[k] for k in range(K) if mask >> k & 1]
        lam = C[[k for k in range(K) if mask >> k & 1]].sum(0)
        E = int(np.abs(lam).sum())
        energies[mask] = E
        # JY matrix model
        X = np.zeros((a + 1, b + 1), dtype=np.int64)
        for k in range(K):
            if mask >> k & 1:
                X[ex[k]] = 1
        if int(np.abs(M @ X @ N.T).sum()) != E:
            model_mismatch += 1
        # FFT of adjacency first row
        row = np.isin(gcds, D).astype(float)
        row[0] = 0.0
        ev = np.fft.fft(row)
        if abs(np.abs(ev.real).sum() - E) > 1e-6 * max(1, E) or np.abs(ev.imag).max() > 1e-6:
            fft_mismatch += 1
    order = sorted(energies, key=lambda m: -energies[m])
    Emax = energies[order[0]]
    maximisers = [m for m in order if energies[m] == Emax]
    Dstar = sorted(p ** i * q ** j for i in range(a + 1) for j in range(b + 1) if (i + j) % 2 == 0)
    formula = (n + d_formula(a, p) * d_formula(b, q)) / 2
    best_sets = [sorted(divs[k] for k in range(K) if m >> k & 1) for m in maximisers]
    ok = (len(maximisers) == 1 and best_sets[0] == Dstar and Emax == formula
          and model_mismatch == 0 and fft_mismatch == 0)
    # dense eigen-decomposition of the actual adjacency matrices
    dense_sets = range(1, 1 << K) if n <= 150 else order[:4]
    dense_mismatch = 0
    idx = np.arange(n)
    G = np.vectorize(gcd)((idx[:, None] - idx[None, :]) % n, n)
    for m in dense_sets:
        D = [divs[k] for k in range(K) if m >> k & 1]
        A = np.isin(G, D).astype(float)
        np.fill_diagonal(A, 0.0)
        assert np.array_equal(A, A.T)
        Ed = np.abs(np.linalg.eigvalsh(A)).sum()
        if abs(Ed - energies[m]) > 1e-6 * energies[m]:
            dense_mismatch += 1
    ok = ok and dense_mismatch == 0
    allok &= ok
    print('n=%d=%d^%d*%d^%d: #sets=%d  Emax=%d  formula=%s  #maximisers=%d  argmax=%s  D*=%s'
          % (n, p, a, q, b, (1 << K) - 1, Emax, formula, len(maximisers), best_sets[0], Dstar))
    print('     2nd best E=%d (set %s)  model mismatches=%d  FFT mismatches=%d  dense-eig mismatches=%d (checked %d sets)  %s  %.1fs'
          % (energies[order[len(maximisers)]], sorted(divs[k] for k in range(K) if order[len(maximisers)] >> k & 1),
             model_mismatch, fft_mismatch, dense_mismatch, len(dense_sets), 'OK' if ok else 'FAIL', time.time() - t0))
    sys.stdout.flush()
print('ALL OK:', allok, ' total %.1fs' % (time.time() - t_all))
