"""Parallel driver for generic_prover.py: identical mathematics, but
 (i) sign tests on denominators first try the coefficient test on the expanded denominator (factoring only as fallback);
 (ii) all certificate expressions are generated first and then certified in a multiprocessing pool.
Usage: python3 generic_prover_fast.py a [workers] [K]"""
import itertools, sys, time
import multiprocessing as mp
import sympy as sp
import generic_prover as G

s, t = G.s, G.t

def psign(poly_expr):
    pl = sp.Poly(poly_expr, s, t)
    cs = dict(zip(pl.monoms(), pl.coeffs()))
    c0 = cs.get((0, 0), 0)
    if all(v >= 0 for v in cs.values()) and c0 > 0: return 1
    if all(v <= 0 for v in cs.values()) and c0 < 0: return -1
    return None

def sign_on_fast(expr, region):
    e = sp.together(sp.expand(G.sub(expr, region)))
    num, den = sp.fraction(e)
    num = sp.expand(num); den = sp.expand(den)
    if num == 0: return 0
    sd = psign(den)
    if sd is None:
        fl = sp.factor_list(den); sd = sp.sign(fl[0])
        for f, k in fl[1]:
            ps = psign(f)
            if ps is None: return None
            sd *= ps ** k
    sn = psign(num)
    return None if sn is None else int(sn * sd)

G.sign_on = sign_on_fast            # used for sign determinations inside the generator (cached below)
_cache = {}
def cached_sign(expr, region):
    key = (sp.srepr(expr), region)
    if key not in _cache: _cache[key] = sign_on_fast(expr, region)
    return _cache[key]
G.sign_on = cached_sign

class Collector(G.Prover):
    """Instead of certifying on the spot, record (name, expr, region) tasks: each must be certified positive."""
    def __init__(self, a, K=4):
        super().__init__(a, K)
        self.tasks = []
    def certify_all(self, name, base, alts, region):
        for combo in itertools.product(*alts) if alts else [()]:
            self.tasks.append((name, base + sum(combo), region))
        return True

def work(task):
    name, expr, region = task
    try:
        return (name, region, sign_on_fast(expr, region) == 1)
    except Exception as e:
        return (name, region, False)

if __name__ == "__main__":
    a = int(sys.argv[1]); workers = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    K = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    t0 = time.time()
    C = Collector(a, K)
    C.lemmaS(); nS = C.nchecks; failS = list(C.fails)       # lemmaS certifies directly (small)
    C.FD1(); nF = len(C.tasks)
    C.chains(); nC = len(C.tasks) - nF
    C.eq_forcing()
    print(f"a={a}: generated tasks FD1={nF}, chains={nC} (S direct checks={nS}, S failures={len(failS)}, "
          f"EQ/other direct failures={len(C.fails) - len(failS)}), cheap={ {r: len(v) for r, v in C.cheap.items()} } "
          f"[{time.time()-t0:.0f}s]", flush=True)
    with mp.Pool(workers) as pool:
        res = pool.map(work, C.tasks, chunksize=8)
    bad = [(n, r) for n, r, ok in res if not ok]
    print(f"a={a}: certified {len(res)} tasks, failures {len(bad)}; direct-check failures {len(C.fails)}; total time {time.time()-t0:.0f}s", flush=True)
    for b in (bad + C.fails)[:30]: print("   FAIL:", b)
