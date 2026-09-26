# Numerical spot check of [BMS, Thm 2.1] on random generalized sun graphs carrying at least
# one pendant path with >= 3 edges: an eigenvalue must lie in (1, 2cos(pi/9)] and one in [-2cos(pi/9), -1).
import random, math
import numpy as np
rng = random.Random(5); rho = 2*math.cos(math.pi/9); bad = 0; T = 3000
for t in range(T):
    b = rng.randint(3, 12); edges = [(k, (k+1) % b) for k in range(b)]; n = b
    paths = []
    for k in range(b):
        for _ in range(rng.choice([0, 0, 1, 2, 3])):
            paths.append((k, rng.choice([1, 1, 2, 2, 3, 4, 5])))
    paths.append((rng.randrange(b), rng.choice([3, 4, 5, 6])))   # ensure a long pendant path
    for k, L in paths:
        prev = k
        for i in range(L):
            edges.append((prev, n)); prev = n; n += 1
    A = np.zeros((n, n))
    for u, v in edges: A[u, v] = A[v, u] = 1
    ev = np.linalg.eigvalsh(A)
    if not (np.any((ev > 1 + 1e-9) & (ev <= rho + 1e-9)) and np.any((ev < -1 - 1e-9) & (ev >= -rho - 1e-9))):
        bad += 1
print("graphs", T, "violations", bad)
