#!/usr/bin/env python3
"""Exact confirmation of sunD/sunD2 candidates: SymPy characteristic polynomial of the full
adjacency matrix, factored over Z; groups candidate sequences into dihedral classes.
Usage: confirm_D.py LOG [LOG ...]"""
import re, sys
import sympy as sp
from validate_D import adjacency

def canon(seq):
    b = len(seq)
    imgs = []
    for s in range(b):
        imgs.append(tuple(seq[(s + k) % b] for k in range(b)))
        imgs.append(tuple(seq[(s - k) % b] for k in range(b)))
    return min(imgs)

x = sp.symbols('x')
classes = {}
for fn in sys.argv[1:]:
    for line in open(fn):
        if not line.startswith('CAND'):
            continue
        pairs = [tuple(map(int, m)) for m in re.findall(r'\((\d+),(\d+)\)', line)]
        c = canon(pairs)
        classes.setdefault(c, 0)
        classes[c] += 1
for c, cnt in sorted(classes.items(), key=lambda t: (len(t[0]), sum(p + 2 * q for p, q in t[0]))):
    b = len(c); p = [a for a, _ in c]; q = [bb for _, bb in c]
    A = sp.Matrix(adjacency(b, p, q))
    cp = A.charpoly(x).as_expr()
    fl = sp.factor_list(cp)
    integral = all(sp.degree(f, x) == 1 for f, _ in fl[1])
    roots = sorted(((-f.subs(x, 0) if sp.degree(f, x) == 1 else None), m) for f, m in fl[1] if sp.degree(f, x) == 1)
    print(f"b={b} n={A.shape[0]} class={c} sequences_in_logs={cnt} integral={integral} spectrum={[(int(r), m) for r, m in roots]}")
