"""DLX with randomised restarts (node budget per attempt) for a CM of S_r."""
import sys, json, os, random, itertools, time
from group_cm_dlx import compose, select, deselect

class Budget(Exception): pass

def solve(X, Y, sol, rnd, budget):
    if not X: return True
    budget[0] -= 1
    if budget[0] < 0: raise Budget
    # MRV with random tie-break
    best = None; bl = None
    for col, rows in X.items():
        l = len(rows)
        if bl is None or l < bl or (l == bl and rnd.random() < 0.3):
            best, bl = col, l
            if l <= 1: break
    rows = list(X[best]); rnd.shuffle(rows)
    for r in rows:
        sol.append(r); cols = select(X, Y, r)
        if solve(X, Y, sol, rnd, budget): return True
        deselect(X, Y, r, cols); sol.pop()
    return False

def main(r, tlimit, node_budget):
    sys.setrecursionlimit(100000)
    G = list(itertools.permutations(range(r))); m = len(G)
    idx = {g: k for k, g in enumerate(G)}
    Y = {(x, y): [('x', x), ('y', y), ('z', idx[compose(G[x], G[y])])] for x in range(m) for y in range(m)}
    t0 = time.time(); seed = 100
    while time.time() - t0 < tlimit:
        X = {}
        for row, cols in Y.items():
            for col in cols: X.setdefault(col, set()).add(row)
        sol = []; rnd = random.Random(seed)
        try:
            if solve(X, Y, sol, rnd, [node_budget]):
                phi = dict(sol)
                assert len(phi) == m and len(set(phi.values())) == m
                assert len({idx[compose(G[x], G[phi[x]])] for x in range(m)}) == m
                return [[list(G[x]), list(G[phi[x]])] for x in range(m)], seed
        except Budget:
            pass
        print(f"seed {seed} failed at {time.time()-t0:.0f}s", flush=True)
        seed += 1
    return None, None

if __name__ == "__main__":
    r = int(sys.argv[1]); tl = int(sys.argv[2]); nb = int(sys.argv[3])
    out, seed = main(r, tl, nb)
    if out is None: print("no solution within time"); sys.exit(1)
    dest = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "certificates", f"cm_S{r}.json")
    if os.path.exists(dest): dest = dest.replace(".json", "_restart.json")
    json.dump(out, open(dest, "w")); print(f"S_{r}: CM found (seed {seed}) -> {dest}")
