# Referee check of PROOF.md Lemma 2 (mult<=2 and monodromy criterion), Lemma 3 (exact formulas for
# mult(0), mult(+-1)), Lemma 4 (moments) and of the referee's own pruning bound, against the exact
# characteristic polynomial (sympy) of the full adjacency matrix.  Biased random sampling with
# small p_k, q_k so that the special cases (vanishing continuants, even gaps) actually occur.
import random, sys
import sympy as sp
from fractions import Fraction as F
x = sp.symbols('x')
def build(b, p, q):
    edges = [(k, (k+1) % b) for k in range(b)]; n = b
    for k in range(b):
        for _ in range(p[k]): edges.append((k, n)); n += 1
        for _ in range(q[k]): edges.append((k, n)); edges.append((n, n+1)); n += 2
    A = [[0]*n for _ in range(n)]
    for u, v in edges: A[u][v] = A[v][u] = 1
    return n, A, edges
def mult_all(cp):
    P = sp.Poly(cp, x); out = {}
    for m in range(-12, 13):
        e = 0
        while True:
            qq, rr = sp.div(P, sp.Poly(x - m, x))
            if rr.is_zero: P = qq; e += 1
            else: break
        out[m] = e
    return out
def delta0(b, p):
    K = [k for k in range(b) if p[k] > 0]
    if not K: return 2 if b % 4 == 0 else 0
    d = 0
    for i in range(len(K)):
        g = (K[i+1] - K[i]) if i+1 < len(K) else K[0] + b - K[i]
        if g % 2 == 0: d += 1
    return d
def matmul(X, Y): return [[X[0][0]*Y[0][0]+X[0][1]*Y[1][0], X[0][0]*Y[0][1]+X[0][1]*Y[1][1]],[X[1][0]*Y[0][0]+X[1][1]*Y[1][0], X[1][0]*Y[0][1]+X[1][1]*Y[1][1]]]
def monodromy(cs):
    M = [[F(1),F(0)],[F(0),F(1)]]
    for c in cs: M = matmul([[F(c), F(-1)],[F(1), F(0)]], M)
    return M
def dim_periodic(cs):
    M = monodromy(cs)
    if M == [[1,0],[0,1]]: return 2
    return 1 if M[0][0] + M[1][1] == 2 else 0
def delta_pm(b, p, q, s):   # s = +1 or -1
    Kq = [k for k in range(b) if q[k] > 0]
    c = [s*(1 - p[k]) for k in range(b)]
    if not Kq: return dim_periodic(c)
    d = 0
    for i in range(len(Kq)):
        a = Kq[i]; e = Kq[i+1] if i+1 < len(Kq) else Kq[0] + b
        # x_a = 0, x_{a+1} = 1, recurrence x_{k+1} = c_k x_k - x_{k-1} for k = a+1..e-1; need x_e = 0
        xp, xc = 0, 1
        for k in range(a+1, e):
            xp, xc = xc, c[k % b]*xc - xp
        if xc == 0: d += 1
    return d
random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
T = int(sys.argv[1]); bad = 0; stats = {'d0>0':0,'dpm>0':0,'mult2':0,'mult1':0}
for t in range(T):
    b = random.randint(3, 14)
    mode = random.random()
    p = [0]*b; q = [0]*b
    for k in range(b):
        if mode < 0.35: p[k] = random.choice([0,0,1,2,3])
        elif mode < 0.6: q[k] = random.choice([0,0,1,2])
        else:
            p[k] = random.choice([0,0,0,1,2,3]); q[k] = random.choice([0,0,0,1,2])
    if random.random() < 0.4:   # rotationally / reflection symmetric configurations -> repeated eigenvalues
        divs = [d for d in range(1, b+1) if b % d == 0 and d < b]
        d = random.choice(divs)
        p = [p[k % d] for k in range(b)]; q = [q[k % d] for k in range(b)]
        if random.random() < 0.5:
            p = [p[(-k) % b] if k % 2 else p[k] for k in range(b)]
    if sum(p) + sum(q) == 0: p[0] = 1
    n, A, E = build(b, p, q)
    if n > 60: continue
    cp = sp.Matrix(A).charpoly(x).as_expr()
    mu = mult_all(cp)
    P = sum(p); Q = sum(q); Kp = sum(1 for v in p if v); Kq = sum(1 for v in q if v)
    d0 = delta0(b, p); dp = delta_pm(b, p, q, 1); dm = delta_pm(b, p, q, -1)
    # Lemma 3 exact
    m0f = P - Kp + d0; mpf = (Q - Kq) + dp; mmf = (Q - Kq) + dm
    if (mu[0], mu[1], mu[-1]) != (m0f, mpf, mmf):
        bad += 1; print('LEMMA3 FAIL', b, p, q, (mu[0], mu[1], mu[-1]), (m0f, mpf, mmf))
    # referee pruning bound
    rlb = b + Kp - d0 - (4 if Kq == 0 else 0)
    r = n - mu[0] - mu[1] - mu[-1]
    if r < rlb: bad += 1; print('BOUND FAIL', b, p, q, r, rlb)
    # Lemma 2
    for m in list(range(-12, -1)) + list(range(2, 13)):
        cs = [F(m) - F(p[k], m) - F(q[k]*m, m*m - 1) for k in range(b)]
        pred = dim_periodic(cs)
        if mu[m] != pred: bad += 1; print('LEMMA2 FAIL', b, p, q, m, mu[m], pred)
        if mu[m] == 2: stats['mult2'] += 1
        if mu[m] == 1: stats['mult1'] += 1
    # Lemma 4 moments via exact traces of A^2, A^4 (and A^3 for triangles)
    deg = [0]*n
    for u, v in E: deg[u] += 1; deg[v] += 1
    M = sp.Matrix(A); M2 = M*M; t4 = (M2*M2).trace(); t2 = M2.trace()
    pred4 = 2*sum(d*d for d in deg) - 2*len(E) + (8 if b == 4 else 0)
    if t2 != 2*n or t4 != pred4: bad += 1; print('MOMENT FAIL', b, p, q, t2, t4, pred4)
    if d0 > 0: stats['d0>0'] += 1
    if dp + dm > 0: stats['dpm>0'] += 1
print('checked', T, 'bad', bad, stats)
