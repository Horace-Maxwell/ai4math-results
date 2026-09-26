"""Does the first-deviation method extend to general a?  Column path over q, F-side T_a(p), a+b even.
(FD1_a) at the exact anti-checkerboard state zeta_J = sigma*mu_{b-2-J}*s_a, every deviation c != continuation has s_J > 2 delta_a(p) rho.
(cheap)  last columns c_b (c_b[a] = -1, c_b != anti last column) with rho*Delta(c_b) < 2 delta_a rho, i.e. Delta(c_b) < 2 delta_a(p).
(S_a)   one-step bound s >= 0 at random states in the cube (q = 3 is the unproved case for a >= 3)."""
import itertools, random, sys
from fractions import Fraction as Fr
from core import T, mus, dfun, delta_last
def hfun(Q, mu, A, B):
    return Q * abs(A - B) + mu * abs(B + Q * A) - (Q - mu) * abs(B) - Q * (1 + mu) * abs(A)
def mv(M, c): return [sum(M[i][k] * c[k] for k in range(len(c))) for i in range(len(M))]
def surplus(M, Dp, Q, q, mu, c, zeta):
    A = mv(M, c); B = mv(M, zeta)
    return Q * (1 + mu) / q * (Dp - sum(abs(x) for x in A)) - sum(hfun(Q, mu, A[i], B[i]) for i in range(len(A))) / q
def fd1(a, p, q, bs):
    p = Fr(p); q = Fr(q); Q = q - 1
    M = T(a, p); Dp = dfun(a, p); da = delta_last(a, p)
    sa = [(-1) ** i for i in range(a + 1)]
    cols = list(itertools.product([1, -1], repeat=a + 1))
    worst = None
    for b in bs:
        if (a + b) % 2: continue
        mu = mus(b + 2, q); rho = mu[b - 1]; need = 2 * da * rho
        for J in range(b):
            # anti-checkerboard column j is -(-1)^j s_a ; state after columns J+1..b: sign of column J+1, magnitude mu_{b-2-J}
            sig = -(-1) ** (J + 1)
            zeta = [sig * mu[b - 2 - J] * x for x in sa]
            cont = [-sig * x for x in sa]
            for c in cols:
                if list(c) == cont: continue
                r = surplus(M, Dp, Q, q, mu[J - 1], c, zeta) / need
                if worst is None or r < worst[0]: worst = (r, b, J, c)
    return worst
def cheap(a, p):
    p = Fr(p); M = T(a, p); Dp = dfun(a, p); da = delta_last(a, p)
    out = []
    for c in itertools.product([1, -1], repeat=a + 1):
        if c[a] != -1: continue
        D = Dp - sum(abs(x) for x in mv(M, c))
        if D < 2 * da: out.append((c, D, 2 * da))
    return out
if __name__ == "__main__":
    for a in [2, 3, 4]:
        bs = [b for b in range(1, 13) if (a + b) % 2 == 0]
        for (p, q) in [(5, 3), (7, 3), (11, 3), (3, 5), (3, 7), (5, 7), (7, 5), (101, 3), (3, 101)]:
            w = fd1(a, p, q, bs)
            print(f"a={a} p={p} q={q}: FD1_a min ratio {float(w[0]):.4f} at b={w[1]} J={w[2]} dev={w[3]}{'   <-- FAILS' if w[0] <= 1 else ''}")
            sys.stdout.flush()
        for p in [5, 3, 101]:
            ch = cheap(a, p)
            print(f"a={a} p={p}: last columns with Delta < 2 delta_a (need chain analysis): {[(c, str(D)) for c, D, _ in ch]}")
    # S_a at q = 3 (random states), a = 3, 4
    random.seed(5)
    for a in [3, 4]:
        bad = 0; n = 0
        for trial in range(400):
            p = Fr(random.choice([5, 7, 11, 13])) ; q = Fr(3); Q = q - 1
            M = T(a, p); Dp = dfun(a, p)
            mu = Fr(random.randint(0, 1000), 1000)
            zeta = [Fr(random.randint(-1000, 1000), 1000) for _ in range(a + 1)]
            for c in itertools.product([1, -1], repeat=a + 1):
                s = surplus(M, Dp, Q, q, mu, c, zeta); n += 1; bad += s < 0
        print(f"S_a at q=3, a={a}: random states {n}, negative surplus {bad}")
