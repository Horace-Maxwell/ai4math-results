#!/usr/bin/env python3
"""Sharded driver for implementation A (swtrees_A.py): generate all trees up to N by canonical
augmentation (deterministic order), then check only the trees of order N with index % m == r."""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from swtrees_A import trees_upto, check_tree
N, m, r = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
t0 = time.time()
for n, trees in trees_upto(N):
    if n < N: continue
    ok = 0; bad = []; cnt = 0
    for idx, adj in enumerate(trees):
        if idx % m != r: continue
        cnt += 1
        res, d, s = check_tree(adj, n)
        if res: ok += 1
        else: bad.append(adj)
    print(f"n={n} shard={r}/{m} total_trees={len(trees)} checked={cnt} certified_exact={ok} fail={len(bad)} time={time.time()-t0:.1f}s", flush=True)
    for b in bad[:5]: print('  FAIL', b, flush=True)
