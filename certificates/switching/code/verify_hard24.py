# Exact verification for the n=24 "hard" trees printed by swtrees_print (shard 0):
#  (1) the printed switching s is good (exact Bareiss rank over Q = d, d from sympy gcd);
#  (2) NO switching with min(|U|, n-|U|) <= 3 is good (exact), i.e. >= 4 switched vertices are needed;
#  (3) the minimum is found by exact search over |U| = 4.
import os, sys, re, itertools, sympy
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from swtrees_A import charpoly, exact_rank, krylov_rows
def layout_to_adj(layout):
    n = len(layout); adj = [[] for _ in range(n)]; stack = []
    for i in range(n):
        il = layout[i]
        if stack:
            j = stack[-1]
            while layout[j] >= il:
                stack.pop(); j = stack[-1]
            adj[i].append(j); adj[j].append(i)
        stack.append(i)
    return adj
x = sympy.Symbol('x')
def analyse(layout, sstr, max_trees_detail=True):
    adj = layout_to_adj(layout); n = len(adj)
    phi = charpoly(adj, n); P = sympy.Poly(list(reversed(phi)), x, domain='ZZ')
    d = n - sympy.gcd(P, P.diff(x)).degree()
    good = lambda s: exact_rank(krylov_rows(adj, s, d)) == d
    s_print = [1 if ch == '+' else -1 for ch in sstr]
    ok_print = good(s_print)
    le3 = [U for k in range(4) for U in itertools.combinations(range(n), k) if good([-1 if i in U else 1 for i in range(n)])]
    four = None
    if not le3:
        for U in itertools.combinations(range(n), 4):
            if good([-1 if i in U else 1 for i in range(n)]): four = U; break
    fac = sympy.factor_list(P.as_expr())[1]
    degs = [v for v in range(n)]
    edges = sorted((min(i, j), max(i, j)) for i in range(n) for j in adj[i] if i < j)
    return dict(n=n, d=d, printed_s_good=ok_print, good_le3=len(le3), first_good_4set=four,
                factors=[(str(f), m) for f, m in fac], edges=edges)
if __name__ == '__main__':
    lines = [l for l in open(sys.argv[1]) if l.startswith('HARD')]
    m = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    r = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    for idx, l in enumerate(lines):
        if idx % m != r: continue
        mm = re.match(r'HARD .*level seq:([\d ]+)\| good s:([+-]+)', l.strip())
        layout = list(map(int, mm.group(1).split())); sstr = mm.group(2)
        res = analyse(layout, sstr)
        print('tree#%d' % idx, res, flush=True)
