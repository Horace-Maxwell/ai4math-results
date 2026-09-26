"""Referee-2: re-run the AUTHORS' code (generic_prover_fast.Collector / work, unmodified, imported read-only) on a sample.

 1. Regenerate the full task list for a (single process) and compare its size with the authors' log; re-run all direct checks
    performed during generation (Lemma S_a, chain-alone, full chain, EQ) and report their failures.
 2. Certify a random sample of the generated tasks with the authors' work() (sign_on_fast), in a pool of <= W workers.
 3. Evaluate every sampled task expression exactly at 3 random rational points of its region (sanity: must be > 0).
Usage: python3 t8_rerun_authors.py a nsample workers
"""
import sys, os, random, time
sys.path.insert(0, os.path.abspath('..'))
import sympy as sp
from multiprocessing import Pool
import generic_prover as GP
import generic_prover_fast as GF

def evalpt(args):
    name, expr, region, pts = args
    vals = []
    for (sv, tv) in pts:
        e = GP.sub(expr, region).subs({GP.s: sv, GP.t: tv})
        vals.append(sp.Rational(e))
    return min(vals)

if __name__ == "__main__":
    a = int(sys.argv[1]); nsample = int(sys.argv[2]); W = int(sys.argv[3])
    out = open(f'logs/t8_rerun_authors_a{a}.log', 'w')
    def log(*x):
        s = ' '.join(str(y) for y in x); print(s, flush=True); out.write(s + '\n'); out.flush()
    t0 = time.time()
    C = GF.Collector(a, 4)
    C.lemmaS(); nS = C.nchecks; failS = list(C.fails)
    C.FD1(); nF = len(C.tasks)
    C.chains(); nC = len(C.tasks) - nF
    C.eq_forcing()
    log(f"a={a}: regenerated tasks FD1={nF}, chains={nC}; S direct checks={nS} (failures {len(failS)}); "
        f"direct failures total {len(C.fails)}; cheap={ {r: len(v) for r, v in C.cheap.items()} } [{time.time()-t0:.0f}s]")
    rnd = random.Random(2026 + a)
    idx = sorted(rnd.sample(range(len(C.tasks)), min(nsample, len(C.tasks))))
    # stratify: make sure every task family appears
    fams = {}
    for i, (n, e, r) in enumerate(C.tasks):
        fams.setdefault((n.split(' ')[0], r), []).append(i)
    for key, lst in fams.items():
        idx.extend(rnd.sample(lst, min(10, len(lst))))
    idx = sorted(set(idx))
    sample = [C.tasks[i] for i in idx]
    log(f"a={a}: sample of {len(sample)} tasks (families: { {k: len(v) for k, v in fams.items()} })")
    with Pool(W) as pool:
        res = pool.map(GF.work, sample, chunksize=4)
    bad = [(n, r) for n, r, ok in res if not ok]
    log(f"a={a}: authors' certificate re-run on the sample: {len(res) - len(bad)} certified, {len(bad)} failed "
        f"[{time.time()-t0:.0f}s]")
    for b in bad[:20]: log("   FAIL", b)
    # numeric sanity at random points
    pts_args = []
    for (n, e, r) in sample:
        pts = [(sp.Rational(rnd.randint(0, 40), rnd.randint(1, 5)) if r == 'big' else 0, sp.Rational(rnd.randint(0, 40), rnd.randint(1, 5)))
               for _ in range(3)] + [(0, 0)]
        pts_args.append((n, e, r, pts))
    with Pool(W) as pool:
        mins = pool.map(evalpt, pts_args, chunksize=4)
    neg = [pts_args[i][0] for i, v in enumerate(mins) if v <= 0]
    log(f"a={a}: exact evaluation of sampled task expressions at 4 points each (incl. the region corner): "
        f"{len(mins) - len(neg)} positive, {len(neg)} non-positive; min value {float(min(mins)):.4g} [{time.time()-t0:.0f}s]")
