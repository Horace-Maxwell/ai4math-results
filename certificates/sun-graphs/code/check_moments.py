# Sanity check of the trace identities used in Lemma 4 / Theorem 2 on random generalized sun graphs:
#   tr A^2 = 2n, tr A^4 = 2n + 2 sum d(d-1) (b != 4), tr A^L = 0 for odd L < b, tr A^b = 2b (b odd).
import numpy as np, random
random.seed(7); bad = 0; cnt = 0
for t in range(400):
    b = random.randint(3, 11)
    if b == 4: continue
    p = [random.randint(0, 4) for _ in range(b)]; q = [random.randint(0, 3) if random.random() < .4 else 0 for _ in range(b)]
    n = b + sum(p) + 2 * sum(q); A = np.zeros((n, n), dtype=np.int64); nxt = b
    for k in range(b): A[k, (k+1) % b] = A[(k+1) % b, k] = 1
    for k in range(b):
        for _ in range(p[k]): A[k, nxt] = A[nxt, k] = 1; nxt += 1
        for _ in range(q[k]): A[k, nxt] = A[nxt, k] = 1; A[nxt, nxt+1] = A[nxt+1, nxt] = 1; nxt += 2
    d = A.sum(1); M = np.eye(n, dtype=np.int64); tr = {}
    for L in range(1, max(b, 4) + 1): M = M @ A; tr[L] = int(np.trace(M))
    ok = tr[2] == 2*n and tr[4] == 2*n + 2*int((d*(d-1)).sum())
    if b % 2 == 1: ok = ok and all(tr[L] == 0 for L in range(1, b, 2)) and tr[b] == 2*b
    cnt += 1; bad += (not ok)
print("graphs", cnt, "identity failures", bad)
