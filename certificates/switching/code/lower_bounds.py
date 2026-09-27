# Exact lower bounds for a(n) := max over trees T on n vertices of min{ min(|U|,n-|U|) : s = 1 - 2*1_U good }.
# For each n, a witness tree is taken from swtrees_witness (first tree in WROM order whose certified category
# is >= target); here we check EXACTLY (sympy gcd for d, Bareiss rank over Q) that no switching with
# min(|U|,n-|U|) <= target-1 is good, which proves a(n) >= target. Upper bounds a(n) <= target come from the
# exhaustive certified runs of implementation B (logs/swtrees_B*.out).
import os, sys, subprocess, itertools, sympy
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from swtrees_A import charpoly, exact_rank, krylov_rows
from verify_hard24 import layout_to_adj
x = sympy.Symbol('x')
CODE = os.path.dirname(os.path.abspath(__file__)) + '/'
targets = {3: 1, 4: 1}
for n in range(5, 13): targets[n] = 2
targets[13] = 3; targets[14] = 2
for n in range(15, 24): targets[n] = 3
for n in sorted(targets):
    t = targets[n]
    out = subprocess.run([CODE + 'swtrees_witness', str(n), str(t)], capture_output=True, text=True).stdout.strip()
    layout = list(map(int, out.split('level seq:')[1].split()))
    adj = layout_to_adj(layout)
    phi = charpoly(adj, n); P = sympy.Poly(list(reversed(phi)), x, domain='ZZ')
    d = n - sympy.gcd(P, P.diff(x)).degree()
    good_small = []
    for k in range(t):
        for U in itertools.combinations(range(n), k):
            s = [-1 if i in U else 1 for i in range(n)]
            if exact_rank(krylov_rows(adj, s, d)) == d: good_small.append(U)
    # exhibit an exact good switching with exactly t flips
    ex = None
    for U in itertools.combinations(range(n), t):
        s = [-1 if i in U else 1 for i in range(n)]
        if exact_rank(krylov_rows(adj, s, d)) == d: ex = U; break
    edges = sorted((min(i, j), max(i, j)) for i in range(n) for j in adj[i] if i < j)
    print(f"n={n} target={t} witness_layout={layout} d={d} good_with_<{t}_flips={len(good_small)} exact_good_{t}-set={ex} => a(n)>={t} {'PROVED' if not good_small and ex else 'NOT PROVED'} edges={edges}", flush=True)
