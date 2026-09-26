# Exact check (sympy): number of eigenvalues > 1 (with multiplicity) of C_b plus one attachment
# (pendant vertex or pendant P_2), and of C_b plus two attachments at distinct cycle vertices.
import sympy as sp, sys
def graph(b, atts):   # atts: list of (vertex, kind) kind 1 = P1, 2 = P2
    n = b + sum(k for _, k in atts); A = sp.zeros(n, n); nxt = b
    for i in range(b): A[i,(i+1)%b] = A[(i+1)%b,i] = 1
    for v,k in atts:
        A[v,nxt] = A[nxt,v] = 1
        if k == 2: A[nxt,nxt+1] = A[nxt+1,nxt] = 1
        nxt += k
    return A
def n_gt(A, t):
    """exact number of eigenvalues > t (with multiplicity): Sturm counts on the square-free factors"""
    x = sp.symbols('x'); P = sp.Poly(A.charpoly(x).as_expr(), x)
    tot = 0
    for f, e in P.sqf_list()[1]:
        c = f.count_roots(t, 10**6)            # distinct roots of f in [t, 10^6]
        if f.eval(t) == 0: c -= 1              # exclude t itself
        tot += e * c
    return tot
for b in [int(a) for a in sys.argv[1:]]:
    print("b=%d  N>1(C_b)=%d" % (b, n_gt(graph(b, []), 1)))
    for k in (1, 2): print("  one attachment kind P%d: N>1 = %d" % (k, n_gt(graph(b, [(0, k)]), 1)))
    worst = None
    for d in range(1, b//2 + 1):
        for k1, k2 in [(1,1),(1,2),(2,2)]:
            v = n_gt(graph(b, [(0,k1),(d,k2)]), 1)
            worst = v if worst is None else min(worst, v)
            print("  two attachments at distance %d kinds (P%d,P%d): N>1 = %d" % (d, k1, k2, v))
    print("  min over two distinct-vertex attachments:", worst)
