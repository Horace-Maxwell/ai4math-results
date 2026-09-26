"""Find a complete mapping of S_r by exact cover (Knuth's Algorithm X, dict-of-sets
version, MRV column choice, randomised row order).  Rows: pairs (x, y) meaning
alpha(x) = y; columns: ('x',x), ('y',y), ('z', x*y).  Output as group_cm_sat.py."""
import sys, json, os, random, itertools, time


def compose(a, b):
    return tuple(b[a[k]] for k in range(len(a)))


def solve(X, Y, solution, rnd, deadline):
    if not X:
        return True
    if time.time() > deadline:
        raise TimeoutError
    c = min(X, key=lambda col: len(X[col]))
    rows = list(X[c])
    rnd.shuffle(rows)
    for r in rows:
        solution.append(r)
        cols = select(X, Y, r)
        if solve(X, Y, solution, rnd, deadline):
            return True
        deselect(X, Y, r, cols)
        solution.pop()
    return False


def select(X, Y, r):
    cols = []
    for j in Y[r]:
        for i in X[j]:
            for k in Y[i]:
                if k != j:
                    X[k].remove(i)
        cols.append(X.pop(j))
    return cols


def deselect(X, Y, r, cols):
    for j in reversed(Y[r]):
        X[j] = cols.pop()
        for i in X[j]:
            for k in Y[i]:
                if k != j:
                    X[k].add(i)


def main(r, seed=0, tlimit=600):
    sys.setrecursionlimit(100000)
    G = list(itertools.permutations(range(r)))
    m = len(G)
    idx = {g: k for k, g in enumerate(G)}
    Y = {}
    for x in range(m):
        for y in range(m):
            z = idx[compose(G[x], G[y])]
            Y[(x, y)] = [('x', x), ('y', y), ('z', z)]
    X = {}
    for row, cols in Y.items():
        for col in cols:
            X.setdefault(col, set()).add(row)
    sol = []
    rnd = random.Random(seed)
    ok = solve(X, Y, sol, rnd, time.time() + tlimit)
    assert ok
    phi = dict(sol)
    assert len(phi) == m and len(set(phi.values())) == m
    assert len({idx[compose(G[x], G[phi[x]])] for x in range(m)}) == m
    return [[list(G[x]), list(G[phi[x]])] for x in range(m)]


if __name__ == "__main__":
    r = int(sys.argv[1]); seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    tl = int(sys.argv[3]) if len(sys.argv) > 3 else 600
    t = time.time()
    out = main(r, seed, tl)
    dest = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "certificates", f"cm_S{r}.json")
    if os.path.exists(dest):
        dest = dest.replace(".json", "_dlx.json")
    json.dump(out, open(dest, "w"))
    print(f"S_{r}: complete mapping found by DLX in {time.time()-t:.1f}s -> {dest}")
