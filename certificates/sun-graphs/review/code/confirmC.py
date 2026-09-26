# Exact confirmation of sunC candidates: rebuild the full adjacency matrix, compute and factor the
# characteristic polynomial with sympy, and reduce to dihedral canonical form.
import sys, re, glob
import sympy as sp
x = sp.symbols('x')
def build(b, p, q):
    edges = [(k, (k+1) % b) for k in range(b)]; n = b
    for k in range(b):
        for _ in range(p[k]): edges.append((k, n)); n += 1
        for _ in range(q[k]): edges.append((k, n)); edges.append((n, n+1)); n += 2
    A = [[0]*n for _ in range(n)]
    for u, v in edges: A[u][v] = A[v][u] = 1
    return n, A
def canon(pairs):
    b = len(pairs); best = None
    for r in range(b):
        for refl in (0, 1):
            img = tuple(pairs[(r - k) % b] if refl else pairs[(k + r) % b] for k in range(b))
            if best is None or img > best: best = img
    return best
seen = {}
for fn in sys.argv[1:]:
    for line in open(fn):
        if not line.startswith('CAND'): continue
        b = int(re.search(r'b=(\d+)', line).group(1))
        pairs = [tuple(map(int, t)) for t in re.findall(r'\((\d+),(\d+)\)', line)]
        c = canon(pairs)
        if c in seen: continue
        p = [a for a, _ in pairs]; q = [bb for _, bb in pairs]
        n, A = build(b, p, q)
        f = sp.factor_list(sp.Matrix(A).charpoly(x).as_expr())
        integral = all(sp.degree(g, x) == 1 for g, e in f[1])
        spec = sorted(((-sp.Poly(g, x).all_coeffs()[1] if sp.degree(g, x) == 1 else str(g)), e) for g, e in f[1]) if integral else None
        seen[c] = (b, n, integral, spec)
for c, (b, n, integral, spec) in sorted(seen.items(), key=lambda t: (t[1][0], t[1][1])):
    print('b=%d n=%d canonical=%s integral=%s spec=%s' % (b, n, ' '.join('(%d,%d)' % t for t in c), integral, spec))
print('distinct graphs:', len(seen), ' integral:', sum(1 for v in seen.values() if v[2]))
