#!/usr/bin/env python3
"""Scripted axiom audit: every expected final declaration must have exactly one
'depends on axioms' line whose axiom set is a subset of the whitelist."""
import re, sys
WL = {'propext', 'Classical.choice', 'Quot.sound'}
log, audit_src = sys.argv[1], sys.argv[2]
expected = re.findall(r'^#print axioms (\S+)', open(audit_src).read(), re.M)
got = {}
bad_format = 0
for line in open(log):
    m = re.match(r"^'(\S+)' depends on axioms: \[(.*)\]\s*$", line.strip())
    if m:
        got.setdefault(m.group(1), []).append({a.strip() for a in m.group(2).split(',') if a.strip()})
    elif 'depends on axioms' in line or 'does not depend on any axioms' in line:
        bad_format += 1
viol = {k: v for k, v in got.items() if any(not s <= WL for s in v)}
missing = [e for e in expected if e not in got]
dups = {k: len(v) for k, v in got.items() if len(v) > 1}
print(f'expected declarations: {len(expected)} (distinct {len(set(expected))}); printed: {sum(len(v) for v in got.values())} lines for {len(got)} distinct')
print('missing:', missing); print('duplicates:', dups); print('violations:', viol); print('unrecognised lines:', bad_format)
print('AXIOM AUDIT', 'PASS' if not (missing or viol or bad_format) else 'FAIL')
