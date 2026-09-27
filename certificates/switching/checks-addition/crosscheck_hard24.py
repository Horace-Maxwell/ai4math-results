#!/usr/bin/env python3
"""Added at packaging (27 Sep 2026): the Galois-factor criterion of code/crosscheck_galois.py applied to the
n = 24 trees of a verify_hard24.py log.  For each tree it counts the sets U with |U| <= 3 for which
s = 1 - 2*1_U is good by that criterion (none expected), in the format of logs/crosscheck_galois_all.log.
Usage: python3 crosscheck_hard24.py VERIFY_LOG"""
import ast, os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'code'))
from crosscheck_galois import check

logf = sys.argv[1]
name = os.path.basename(logf)
done = bad = 0
for line in open(logf):
    m = re.match(r"tree#(\d+) (\{.*\})", line.strip())
    if not m:
        continue
    d = ast.literal_eval(m.group(2))
    facs, small = check(d['edges'], d['n'], 3)
    done += 1
    ok = (len(small) == 0) and d['good_le3'] == 0
    bad += 0 if ok else 1
    print('n=%d hard tree %s#%s: good U with |U|<=3: %d -> %s' % (d['n'], name, m.group(1), len(small),
                                                                 'CONFIRMED' if ok else 'MISMATCH'), flush=True)
print('hard trees cross-checked: %d mismatches: %d' % (done, bad))
