"""List near-extremal Y for H1 (Y00 = Yab, value ||Z||-2|Zab|) and H2 (Y00 != Yab, value ||Z||_1), shape (2,b)."""
import sys, numpy as np
from fastenum import all_Y, Zall, target
def fmt(Y):
    return '/'.join(''.join('+' if v > 0 else '-' for v in r) for r in Y)
def run(a, b, p, q, top=8):
    Y = all_Y(a, b)
    Y = Y[Y[:, 0, 0] == 1]          # WLOG Y00 = +1 (symmetry Y -> -Y)
    Z = Zall(Y, p, q)
    Zab = Z[:, a, b]; L1 = np.abs(Z).sum(axis=(1, 2)); Th = target(a, b, p, q)
    for name, mask, val in [('H1', Y[:, a, b] == 1, L1 - 2 * np.abs(Zab)), ('H2', Y[:, a, b] == -1, L1)]:
        idx = np.nonzero(mask)[0]
        v = val[idx]
        order = np.argsort(-v)[:top]
        print(f"== {name} ({a},{b}) p={p} q={q} Theta={Th}")
        for o in order:
            k = idx[o]
            print(f"   gap={Th - v[o]:>10}  Y={fmt(Y[k])}  Zab={Zab[k]}")
    sys.stdout.flush()
if __name__ == "__main__":
    for (b, p, q) in [(2, 5, 3), (2, 3, 5), (4, 5, 3), (4, 3, 5), (4, 7, 3), (4, 11, 3), (4, 5, 7), (4, 3, 7), (4, 101, 3), (4, 3, 101)]:
        run(2, b, p, q)
