# brute-force enumeration of all ideals of a small algebra modulo a prime p (cross-check only)
from itertools import product, combinations
def modp_ideals(A, p):
    n = A.n
    inv = lambda t: pow(t, p - 2, p)
    def modq(fr): return (fr.numerator * inv(fr.denominator % p)) % p
    Tp = [[tuple(modq(t) for t in A.T[i][j]) for j in range(n)] for i in range(n)]
    def mulp(u, v):
        r = [0] * n
        for i in range(n):
            if u[i] == 0: continue
            for j in range(n):
                if v[j] == 0: continue
                for k in range(n): r[k] = (r[k] + u[i] * v[j] * Tp[i][j][k]) % p
        return tuple(r)
    def rank_p(rows):
        M = [list(r) for r in rows]; r = 0
        for col in range(n):
            pr = next((i for i in range(r, len(M)) if M[i][col] % p), None)
            if pr is None: continue
            M[r], M[pr] = M[pr], M[r]
            iv = inv(M[r][col]); M[r] = [(t * iv) % p for t in M[r]]
            for i in range(len(M)):
                if i != r and M[i][col]:
                    f = M[i][col]; M[i] = [(s - f * t) % p for s, t in zip(M[i], M[r])]
            r += 1
        return r
    E = [tuple(1 if k == i else 0 for k in range(n)) for i in range(n)]
    ideals = []
    for k in range(0, n + 1):
        for pivs in combinations(range(n), k):
            free_pos = [(r, col) for r in range(k) for col in range(n) if col > pivs[r] and col not in pivs]
            for vals in product(range(p), repeat=len(free_pos)):
                M = [[0] * n for _ in range(k)]
                for r in range(k): M[r][pivs[r]] = 1
                for (r, col), t in zip(free_pos, vals): M[r][col] = t
                Bm = [tuple(row) for row in M]
                ok = True
                for u in Bm:
                    for e in E:
                        if rank_p(Bm + [mulp(e, u)]) != k: ok = False; break
                    if not ok: break
                if ok: ideals.append(Bm)
    return ideals
