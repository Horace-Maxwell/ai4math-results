"""First deviation from the anti-checkerboard (scanning columns from b down to 0):
columns J+1..b equal (-1)^{j+1} s_2; column J differs.  State zeta_J = (-1)^J mu_{b-2-J} s_2 (exact).
Compute s_J (surplus at column J) for each deviation type and compare with need = 2 delta_p rho_b.
Also J = b (c_b != -s_2 with w_b=-1)."""
import sys
from fractions import Fraction as Fr
from core import T, mus, dfun, delta_last
def hfun(Q, mu, A, B):
    return Q * abs(A - B) + mu * abs(B + Q * A) - (Q - mu) * abs(B) - Q * (1 + mu) * abs(A)
TYPES = {'A': (1, -1, 1), 'B': (1, 1, -1), 'C': (1, -1, -1), 'E': (1, 1, 1)}
def sJ(p, q, b, J, c):
    p = Fr(p); q = Fr(q); Q = q - 1
    M = T(2, p); mu = mus(max(b, 2) + 2, q)
    Dp = dfun(2, p); dp = delta_last(2, p)
    eps = (-1) ** J; m = mu[b - 2 - J]
    s2 = (1, -1, 1)
    zeta = [eps * m * t for t in s2]
    A = [sum(M[i][k] * c[k] for k in range(3)) for i in range(3)]
    B = [sum(M[i][k] * zeta[k] for k in range(3)) for i in range(3)]
    chat = Q * (1 + mu[J - 1]) / q
    F = sum(abs(x) for x in A)
    s = chat * (Dp - F) - sum(hfun(Q, mu[J - 1], A[i], B[i]) for i in range(3)) / q
    need = 2 * dp * mu[b - 1]
    return s, need
if __name__ == "__main__":
    worst = {}
    for (p, q) in [(5, 3), (7, 3), (11, 3), (13, 3), (101, 3), (3, 5), (3, 7), (3, 11), (3, 101), (5, 7), (7, 5), (5, 11), (11, 5), (13, 17)]:
        for b in [2, 4, 6, 8, 10, 20]:
            for J in range(0, b):
                eps = (-1) ** J
                for name, t in TYPES.items():
                    for sg in (1, -1):
                        c = tuple(sg * x for x in t)
                        if name == 'A' and sg == -eps: continue   # this is the anti-checkerboard column itself
                        s, need = sJ(p, q, b, J, c)
                        key = (p, q, name + ('same' if sg == eps else 'opp'), 'J=0' if J == 0 else 'J>0')
                        r = s / need
                        if key not in worst or r < worst[key][0]: worst[key] = (r, b, J)
    for k in sorted(worst):
        r, b, J = worst[k]
        flag = '' if r >= 1 else '   <-- FAILS'
        print(f"p={k[0]:>3} q={k[1]:>3} dev={k[2]:<8} {k[3]}: min s_J/need = {float(r):.4f} (b={b}, J={J}){flag}")
