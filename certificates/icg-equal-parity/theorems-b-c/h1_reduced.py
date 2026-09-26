"""H1-reduced: sum_{u<a} ||row_u(Z)||_1 + q ||T_{b-1}(q) omega'||_1 <= Theta for all Y (omega = Y^T m, m = last row of T_a(p)).
Also the transposed version (reduce on the p side)."""
import sys, numpy as np
from fastenum import all_Y, Zall, target, Tint
def run(a, b, p, q):
    Y = all_Y(a, b)
    Z = Zall(Y, p, q)
    Th = target(a, b, p, q)
    M = Tint(a, p); m = M[a]
    omega = np.einsum('i,nij->nj', m, Y)                  # (N, b+1)
    Nb1 = Tint(b - 1, q) if b >= 1 else None
    red = np.abs(Z[:, :a, :]).sum(axis=(1, 2)) + q * np.abs(np.einsum('vj,nj->nv', Nb1, omega[:, 1:])).sum(axis=1)
    mx = red.max()
    # transposed: reduce on p side: sum_{v<b} ||col_v(Z)||_1 + p ||T_{a-1}(p) psi'||_1, psi = Y n (n = last row of T_b(q))
    N = Tint(b, q); nvec = N[b]
    psi = np.einsum('nij,j->ni', Y, nvec)
    Ma1 = Tint(a - 1, p)
    red2 = np.abs(Z[:, :, :b]).sum(axis=(1, 2)) + p * np.abs(np.einsum('ui,ni->nu', Ma1, psi[:, 1:])).sum(axis=1)
    mx2 = red2.max()
    s = np.array([[(-1) ** (i + j) for j in range(b + 1)] for i in range(a + 1)])
    arg = [Y[k] for k in np.nonzero(red == mx)[0]]
    print(f"({a},{b}) p={p} q={q}: Theta={Th} red_q max={mx} ok={mx <= Th} eqset_ok={len(arg)==2 and all((E==s).all() or (E==-s).all() for E in arg)}; red_p max={mx2} ok={mx2 <= Th}")
    sys.stdout.flush()
for (a, b) in [(1, 1), (2, 2), (1, 3), (3, 1), (2, 4), (4, 2), (3, 3), (2, 3), (3, 2), (1, 2)]:
    for (p, q) in [(5, 3), (3, 5), (7, 3), (5, 7), (11, 3), (3, 11)]:
        run(a, b, p, q)
