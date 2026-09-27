#!/usr/bin/env python3
"""Implementation A' for large n: the EXACT checker of implementation A (swtrees_A.check_tree:
rooted-recursion charpoly, sympy gcd, exact Bareiss rank over Q) applied to trees produced by
networkx's own WROM code (networkx.generators.nonisomorphic_trees private helpers), NOT by the
C port used in implementation B. Sharded: checks trees with index % m == r.
Usage: python3 swtrees_A_nx.py n m r"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from swtrees_A import check_tree
from networkx.generators.nonisomorphic_trees import _next_tree, _next_rooted_tree
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
n, m, r = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
t0 = time.time(); idx = 0; ok = 0; bad = []; cnt = 0
layout = list(range(n // 2 + 1)) + list(range(1, (n + 1) // 2))
while layout is not None:
    layout = _next_tree(layout)
    if layout is not None:
        if idx % m == r:
            adj = layout_to_adj(layout); cnt += 1
            res, d, s = check_tree(adj, n)
            if res: ok += 1
            else: bad.append(list(layout))
        idx += 1
        layout = _next_rooted_tree(layout)
print(f"n={n} shard={r}/{m} total_enumerated={idx} checked={cnt} certified_exact={ok} fail={len(bad)} time={time.time()-t0:.1f}s", flush=True)
for b in bad[:5]: print('  FAIL layout', b, flush=True)
