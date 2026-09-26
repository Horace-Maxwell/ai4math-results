# Validate sunC's characteristic polynomial (mod 2^61-1) against sympy's exact charpoly of the
# full adjacency matrix, on random generalized sun graphs (strong reading, mixed P1/P2).
import random, subprocess, sys, time
import sympy as sp
P1 = 2305843009213693951
C = sys.argv[1]
def build(b, p, q):
    edges = [(k, (k+1) % b) for k in range(b)]
    n = b
    for k in range(b):
        for _ in range(p[k]): edges.append((k, n)); n += 1
        for _ in range(q[k]): edges.append((k, n)); edges.append((n, n+1)); n += 2
    A = [[0]*n for _ in range(n)]
    for u, v in edges: A[u][v] = A[v][u] = 1
    return n, A
random.seed(20260926)
ok = 0; t0 = time.time()
for trial in range(int(sys.argv[2])):
    b = random.randint(3, 12)
    budget = random.randint(0, 41 - b)
    p = [0]*b; q = [0]*b
    while budget > 0:
        k = random.randrange(b)
        if random.random() < 0.5 or budget < 2: p[k] += 1; budget -= 1
        else: q[k] += 1; budget -= 2
    n, A = build(b, p, q)
    x = sp.symbols('x')
    cp = sp.Matrix(A).charpoly(x).all_coeffs()[::-1]  # ascending
    args = [C, 'poly', str(b)] + [str(v) for k in range(b) for v in (p[k], q[k])]
    out = subprocess.run(args, capture_output=True, text=True).stdout.split('\n')[0].split()
    mine = [int(t) for t in out]
    ref = [int(c) % P1 for c in cp]
    if mine != ref:
        print('MISMATCH', b, p, q, n); print(mine[:10]); print(ref[:10]); sys.exit(1)
    ok += 1
print('validated', ok, 'random graphs, max time', round(time.time()-t0, 1), 's')
