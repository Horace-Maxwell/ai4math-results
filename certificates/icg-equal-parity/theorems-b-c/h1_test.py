"""H1 (2D non-corner lemma): ||Z||' - |Z_ab| <= Theta for ALL sign matrices Y, equality iff Y = +-s_a s_b^T.
H2: for Y with Y_ab=-1 and Z_ab > 0: ||Z||_1 <= Theta.
Also split conjecture by regimes."""
import sys, numpy as np
from fastenum import all_Y, Zall, target
def run(a, b, p, q):
    Y = all_Y(a, b)
    Z = Zall(Y, p, q)
    Zab = Z[:, a, b]
    L1 = np.abs(Z).sum(axis=(1, 2))
    Th = target(a, b, p, q)
    h1 = L1 - 2 * np.abs(Zab)
    mx = h1.max(); arg = np.nonzero(h1 == mx)[0]
    s = np.array([[(-1) ** (i + j) for j in range(b + 1)] for i in range(a + 1)])
    eqset = [Y[k] for k in arg]
    ok_eq = len(arg) == 2 and all((abs(E) == 1).all() and ((E == s).all() or (E == -s).all()) for E in eqset)
    # H2
    mask = (Y[:, a, b] == -1) & (Zab > 0)
    h2 = L1[mask].max() if mask.any() else None
    # conjecture check
    G = L1 - 2 * np.maximum(-Zab, 0)
    cm = (Y[:, a, b] == -1)
    gmax = G[cm].max()
    print(f"({a},{b}) p={p} q={q}: Theta={Th}  H1 max={mx} (<=Theta: {mx <= Th}, eq only +-ss^T: {ok_eq})  "
          f"H2 max={h2} (<=Theta: {h2 is None or h2 <= Th})  conj max G={gmax} == Theta: {gmax == Th}")
    sys.stdout.flush()
    return mx <= Th, (h2 is None or h2 <= Th)
if __name__ == "__main__":
    for (a, b) in [(1, 1), (1, 3), (2, 2), (3, 1), (2, 4), (4, 2), (3, 3), (1, 5), (2, 3), (1, 2), (2, 1)]:
        for (p, q) in [(5, 3), (3, 5), (7, 3), (3, 7), (5, 7), (7, 5), (11, 3), (3, 11), (13, 5)]:
            run(a, b, p, q)
