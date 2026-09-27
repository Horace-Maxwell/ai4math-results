#!/usr/bin/env python3
"""Added at packaging (27 Sep 2026): which of the n = 24 trees printed by swtrees_print (HARD lines of
logs/swtrees_print_n24_s*.out) have an exact check in a verify_hard24 log?  Trees are matched by their
edge lists, which verify_hard24.py computes from the level sequence with the same labelling.
With --write-missing FILE it also writes the HARD lines of the unmatched trees to FILE.
Usage: python3 hard24_coverage.py [--write-missing FILE]"""
import ast, glob, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
LOGS = os.path.join(HERE, '..', 'logs')
sys.path.insert(0, os.path.join(HERE, '..', 'code'))
from verify_hard24 import layout_to_adj

def edges_of(line):
    mm = re.match(r'HARD .*level seq:([\d ]+)\| good s:([+-]+)', line.strip())
    adj = layout_to_adj(list(map(int, mm.group(1).split())))
    return tuple(sorted((i, j) for i in range(len(adj)) for j in adj[i] if i < j))

def verified(files):
    out = {}
    for f in files:
        for line in open(f):
            m = re.match(r"tree#(\d+) (\{.*\})", line.strip())
            if m:
                d = ast.literal_eval(m.group(2))
                ok = d['printed_s_good'] and d['good_le3'] == 0 and d['first_good_4set'] is not None
                out.setdefault(tuple(d['edges']), []).append((os.path.basename(f), int(m.group(1)), ok))
    return out

hard = []
for s in range(3):
    for line in open(os.path.join(LOGS, 'swtrees_print_n24_s%d.out' % s)):
        if line.startswith('HARD'):
            hard.append(('s%d' % s, line.rstrip('\n'), edges_of(line)))
orig = verified(sorted(glob.glob(os.path.join(LOGS, 'verify_hard24_*.log'))))
print('HARD trees printed by swtrees_print (n=24):', len(hard), 'distinct:', len({h[2] for h in hard}))
print('entries in logs/verify_hard24_*.log:', sum(len(v) for v in orig.values()), 'distinct trees:', len(orig),
      'checked twice:', sum(1 for v in orig.values() if len(v) > 1))
missing = [h for h in hard if h[2] not in orig]
print('HARD trees without an entry in logs/verify_hard24_*.log:', len(missing), 'shards:', sorted({h[0] for h in missing}))
if len(sys.argv) > 2 and sys.argv[1] == '--write-missing':
    with open(sys.argv[2], 'w') as fh:
        for h in missing:
            fh.write(h[1] + '\n')
add = os.path.join(HERE, 'verify_hard24_missing7.log')
if os.path.exists(add):
    allv = verified(sorted(glob.glob(os.path.join(LOGS, 'verify_hard24_*.log'))) + [add])
    cov = [h for h in hard if h[2] in allv]
    print('with checks-addition/verify_hard24_missing7.log: covered', len(cov), 'of', len(hard),
          '; every entry has the printed s good, no good U with |U|<=3 and a good 4-set:',
          all(ok for v in allv.values() for _, _, ok in v))
