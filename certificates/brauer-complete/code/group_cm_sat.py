"""Find a complete mapping of S_r (group law: compose = 'first a then b')
with CaDiCaL (from the Lean toolchain).  Output: JSON list of pairs
[g, phi(g)] (permutations as lists).  The result is re-checked here and again
by the independent certificate checker at the diagram level."""
import sys, json, subprocess, os, itertools, random, tempfile

# CaDiCaL binary. The original run used the copy in the Lean 4.33.1 toolchain
# (<lean-toolchain>/bin/cadical). Set the environment variable CADICAL to its path,
# or put cadical on PATH.
CADICAL = os.environ.get("CADICAL", "cadical")


def compose(a, b):
    return tuple(b[a[k]] for k in range(len(a)))


def inverse(a):
    inv = [0] * len(a)
    for k, v in enumerate(a):
        inv[v] = k
    return tuple(inv)


def main(r, seed=0, tlimit=600):
    G = list(itertools.permutations(range(r)))
    m = len(G)
    idx = {g: k for k, g in enumerate(G)}
    var = lambda g, h: g * m + h + 1
    nv = m * m
    clauses = []

    def exactly_one(lits):
        nonlocal nv
        clauses.append(list(lits))
        # sequential counter AMO (Sinz)
        n = len(lits)
        s = [0] * n
        for i in range(n - 1):
            nv += 1
            s[i] = nv
        for i in range(n):
            if i < n - 1:
                clauses.append([-lits[i], s[i]])
            if 0 < i < n - 1:
                clauses.append([-s[i - 1], s[i]])
            if i > 0:
                clauses.append([-lits[i], -s[i - 1]])

    for g in range(m):
        exactly_one([var(g, h) for h in range(m)])
    for h in range(m):
        exactly_one([var(g, h) for g in range(m)])
    ginv = [idx[inverse(G[g])] for g in range(m)]
    mul = lambda a, b: idx[compose(G[a], G[b])]
    for z in range(m):
        exactly_one([var(g, mul(ginv[g], z)) for g in range(m)])
    # symmetry fix: phi(identity) = identity (Theorem 3.6-style normalisation is not needed; just a hint)
    path = os.path.join(tempfile.gettempdir(), f"s{r}.cnf")  # CNF scratch file in the system temp directory
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as fh:
        fh.write(f"p cnf {nv} {len(clauses)}\n")
        for c in clauses:
            fh.write(" ".join(map(str, c)) + " 0\n")
    res = subprocess.run([CADICAL, "-q", f"--seed={seed}", "-t", str(tlimit), path], capture_output=True, text=True)
    lines = res.stdout.splitlines()
    status = [l for l in lines if l.startswith("s ")]
    if not status or "UNSATISFIABLE" in status[0] or "SATISFIABLE" not in status[0]:
        raise SystemExit(f"S_{r}: solver status {status}")
    true = set()
    for l in lines:
        if l.startswith("v "):
            for t in l[2:].split():
                t = int(t)
                if 0 < t <= m * m:
                    true.add(t)
    phi = {}
    for t in true:
        g, h = divmod(t - 1, m)
        phi[g] = h
    assert len(phi) == m and len(set(phi.values())) == m
    assert len({mul(g, phi[g]) for g in range(m)}) == m
    return [[list(G[g]), list(G[phi[g]])] for g in range(m)]


if __name__ == "__main__":
    r = int(sys.argv[1])
    out = main(r, seed=int(sys.argv[2]) if len(sys.argv) > 2 else 0, tlimit=int(sys.argv[3]) if len(sys.argv) > 3 else 600)
    dest = os.path.join(os.path.dirname(__file__), "..", "certificates", f"cm_S{r}.json")
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    json.dump(out, open(dest, "w"))
    print(f"S_{r}: complete mapping found and checked, written to {dest}")
