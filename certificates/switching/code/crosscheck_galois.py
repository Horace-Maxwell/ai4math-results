# Independent cross-check (different criterion) of an exact "needs >= k flips" witness:
# s is good  <=>  for every irreducible factor p of the minimal polynomial mu (over Q),
#                 (mu/p)(A) s != 0   (exact integer arithmetic, Horner on the matrix).
# (Proof: (mu/p)(A)s = sum_theta (mu/p)(theta) P_theta s, and (mu/p) vanishes exactly off the roots of p.)
import sys, itertools, sympy, re, ast
x = sympy.Symbol('x')
def check(edges, n, kmax):
    adj = [[] for _ in range(n)]
    for a, b in edges: adj[a].append(b); adj[b].append(a)
    A = sympy.zeros(n, n)
    for a, b in edges: A[a, b] = A[b, a] = 1
    phi = A.charpoly(x).as_expr()
    facs = [sympy.Poly(f, x) for f, m in sympy.factor_list(phi)[1]]
    mu = sympy.Poly(1, x)
    for f in facs: mu = mu * f
    cofs = [sympy.Poly(sympy.quo(mu.as_expr(), f.as_expr(), x), x).all_coeffs() for f in facs]
    def apply_poly(coeffs, s):   # Horner: returns q(A) s with integer vectors
        v = [0] * n
        for c in coeffs:
            v = [sum(v[w] for w in adj[i]) + int(c) * s[i] for i in range(n)]
        return v
    def good(s):
        return all(any(t != 0 for t in apply_poly(c, s)) for c in cofs)
    small = [U for k in range(kmax + 1) for U in itertools.combinations(range(n), k) if good([-1 if i in U else 1 for i in range(n)])]
    return [str(f.as_expr()) for f in facs], small
if __name__ == '__main__':
    logf, idx, kmax = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    for line in open(logf):
        m = re.match(r"tree#(\d+) (\{.*\})", line.strip())
        if m and int(m.group(1)) == idx:
            d = ast.literal_eval(m.group(2))
            facs, small = check(d['edges'], d['n'], kmax)
            four = d['first_good_4set']
            s4 = [-1 if i in four else 1 for i in range(d['n'])]
            print('tree', idx, 'n', d['n'], 'factors', facs)
            print('good switchings with |U| <=', kmax, ':', small)
            # also confirm the 4-set with this criterion
            adj_ok = check(d['edges'], d['n'], -1)
            break
