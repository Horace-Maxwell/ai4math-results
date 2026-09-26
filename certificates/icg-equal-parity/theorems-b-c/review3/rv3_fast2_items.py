"""Referee-3: run the authors' generic_fast2.py (imported read-only, unmodified) with an instrumented certify() that records
every item (one call = one parameter vertex of one inequality), then compare the recorded list with the list that
Proposition 31 requires:
  (F_a)  every c != -s_a, every family of F_a, every vertex of the family's box      (4 families x 12 vertices / 5 x 13)
  (C1)   every last column g needing (C_a), every k = 0..4, every c != (-1)^{k+1} g, every vertex of I_k
         (2 vertices if k = a mod 2, else 3: muinf, mu1 and the isolated point 1)
The certification itself is done by the original method (super().certify), so this is also a full re-run.
Usage: python3 rv3_fast2_items.py a
"""
import collections, itertools, sys, time
sys.path.insert(0, __file__.rsplit('/', 2)[0])          # the authors' folder (read-only import)
import generic_fast2 as gf

a = int(sys.argv[1])
rec = collections.Counter()
cheap_seen = collections.defaultdict(set)


class Instrumented(gf.FastProver):
    def certify(self, name, base, alts):
        rec[(self.R.name, name)] += 1
        return super().certify(name, base, alts)


t0 = time.time()
P = Instrumented(a)
ok = P.run()
print(f'[instrumented run finished in {time.time() - t0:.0f}s; generic_fast2 result ok={ok}]')

sa = tuple((-1) ** i for i in range(a + 1))
vecs = list(itertools.product([1, -1], repeat=a + 1))
bpar = a % 2
regs_even = {'R0': 2, 'R1': 2, 'R2a': 4, 'R2b': 4}
regs_odd = {'B1': 1, 'R0': 2, 'R1': 2, 'R2odd': 4, 'R2even': 4}
regs = regs_even if bpar == 0 else regs_odd
problems = []
# ---- F items
for region in ('big', 'p3'):
    for c in vecs:
        for lab, nv in regs.items():
            key = (region, f'FD1 t={c} {lab}')
            want = 0 if c == tuple(-z for z in sa) else nv
            if rec.get(key, 0) != want:
                problems.append(('F', key, rec.get(key, 0), want))
nF = sum(v for (r, n), v in rec.items() if n.startswith('FD1'))
# ---- C1 items: collect the g's that have chain items
for (region, name), v in rec.items():
    if name.startswith('CH g='):
        g = eval(name[5:name.index(' k=')])
        cheap_seen[region].add(g)
for region in ('big', 'p3'):
    for g in sorted(cheap_seen[region]):
        for k in range(5):
            eps = 1 if k % 2 == 0 else -1
            ny = 2 if (k % 2 == bpar) else 3
            forb = tuple(((-1) ** (k + 1)) * z for z in g)
            for c in vecs:
                tv = tuple(eps * z for z in c)
                key = (region, f'CH g={g} k={k} t={tv}')
                want = 0 if c == forb else ny
                if rec.get(key, 0) != want:
                    problems.append(('C1', key, rec.get(key, 0), want))
nC = sum(v for (r, n), v in rec.items() if n.startswith('CH g='))
other = sorted(set(n.split()[0] for (r, n) in rec if not (n.startswith('FD1') or n.startswith('CH g='))))
print(f'a={a}: recorded items: F {nF}, C1 {nC}; other certify() categories: {other}')
for region in ('big', 'p3'):
    print(f'  region {region}: last columns with chain items ({len(cheap_seen[region])}): {sorted(cheap_seen[region])}')
print(f'  item-list problems vs Proposition 31 structure: {len(problems)}')
for pr in problems[:20]:
    print('   ', pr)
