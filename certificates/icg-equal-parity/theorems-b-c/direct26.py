"""Independent direct check of Theorem B for (2,6) (and (2,8) for a few primes) by exhaustive integer enumeration (numpy int64):
max over Y (Y_{2b} = -1) of G = sum_offcorner |Z| + Z_corner equals Theta, attained exactly by the two conjectured matrices."""
import numpy as np, sys
from fastenum import Tint, target
def run(b, p, q, chunk=1 << 16):
    M = Tint(2, p); N = Tint(b, q)
    nc = 3 * (b + 1); free = nc - 1
    Th = target(2, b, p, q)
    K = np.einsum('ui,vj->uvij', M, N).reshape(nc, nc)      # Z_flat = K @ Y_flat
    best = None; arg = []
    for start in range(0, 1 << free, chunk):
        idx = np.arange(start, min(1 << free, start + chunk), dtype=np.int64)
        Yf = ((idx[:, None] >> np.arange(free)) & 1) * 2 - 1
        Y = np.concatenate([Yf, -np.ones((len(idx), 1), dtype=np.int64)], axis=1)
        Z = Y @ K.T
        G = np.abs(Z[:, :-1]).sum(axis=1) + Z[:, -1]
        mx = G.max()
        if best is None or mx > best: best = mx; arg = [Y[k] for k in np.nonzero(G == mx)[0]]
        elif mx == best: arg += [Y[k] for k in np.nonzero(G == mx)[0]]
    s = np.array([[(-1) ** (i + j) for j in range(b + 1)] for i in range(3)]).reshape(-1)
    anti = -s; trunc = s.copy(); trunc[-1] = -1
    ok_set = len(arg) == 2 and any((a == anti).all() for a in arg) and any((a == trunc).all() for a in arg)
    print(f"(2,{b}) p={p} q={q}: max G = {best}, Theta = {Th}, equal: {best == Th}, maximisers exactly the two: {ok_set}")
    sys.stdout.flush()
    return best == Th and ok_set
if __name__ == "__main__":
    for (p, q) in [(5, 3), (3, 5), (7, 3), (3, 7), (5, 7), (7, 5), (11, 3), (3, 11), (13, 17)]:
        run(6, p, q)
    for (p, q) in [(5, 3), (3, 5)]:
        run(8, p, q)
