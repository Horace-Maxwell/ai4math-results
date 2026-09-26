"""Referee-3: compare, as sets, the last columns that need (C_a) in the three implementations (logs of this review):
rv3_certify (logs/rv3_certify_a*.log), review2/c3_certify re-run (rerun_c3/logs/c3_certify_a*.log) and generic_fast2
instrumented re-run (logs/fast2_items_a*.log).  Region names: R1 = big, R2 = p3."""
import ast, re
ok = True
for a in (5, 6, 7, 8):
    mine = {}
    for line in open(f'logs/rv3_certify_a{a}.log'):
        m = re.match(r'\s+region (R\d) \(.*\): cheap last columns \(\d+\): (\[.*\])', line)
        if m: mine[{'R1': 'big', 'R2': 'p3'}[m.group(1)]] = set(ast.literal_eval(m.group(2)))
    c3 = {}
    for line in open(f'rerun_c3/logs/c3_certify_a{a}.log'):
        m = re.match(r'a=\d+ region=(\w+): cheap last columns (\[.*\]); columns', line)
        if m: c3[m.group(1)] = set(g for g, s in ast.literal_eval(m.group(2)))
    f2 = {}
    for line in open(f'logs/fast2_items_a{a}.log'):
        m = re.match(r'\s+region (\w+): last columns with chain items \(\d+\): (\[.*\])', line)
        if m: f2[m.group(1)] = set(ast.literal_eval(m.group(2)))
    for r in ('big', 'p3'):
        same = mine[r] == c3[r] == f2[r]
        ok &= same
        print(f'a={a} region {r}: rv3 {len(mine[r])}, c3 {len(c3[r])}, fast2 {len(f2[r])} -> identical sets: {same}')
print('ALL IDENTICAL' if ok else 'MISMATCH')
