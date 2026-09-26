"""Driver: parallel exhaustive search via icg_search (C), with Python re-verification.

Usage: python3 run_search.py a b q p1,p2,... [workers]
Prints, for each p, the top masks, whether the checkerboard is the unique maximiser,
and re-verifies the reported energies with the exact Python model.
"""
import subprocess, sys, json, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from icg_model import energy, mask_to_X, X_to_mask, checkerboard

BASE = Path(__file__).parent
BIN = BASE / 'icg_search'


def run(a, b, p, q, workers=16):
    nc = (a + 1) * (b + 1) - 1
    pb = min(nc, 8) if nc > 20 else 0
    npre = 1 << pb
    chunks = [(k * npre // workers, (k + 1) * npre // workers) for k in range(workers)] if pb else [(0, 1)]
    chunks = [c for c in chunks if c[0] < c[1]]

    def job(c):
        out = subprocess.run([str(BIN), str(a), str(b), str(p), str(q), str(pb), str(c[0]), str(c[1])],
                             capture_output=True, text=True, check=True).stdout
        return [tuple(map(int, line.split())) for line in out.split('\n') if line.strip()]
    with ThreadPoolExecutor(len(chunks)) as ex:
        res = [r for part in ex.map(job, chunks) for r in part]
    res.sort(reverse=True)
    return res


if __name__ == '__main__':
    a, b, q = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    ps = [int(t) for t in sys.argv[4].split(',')]
    workers = int(sys.argv[5]) if len(sys.argv) > 5 else 16
    star = X_to_mask(checkerboard(a, b), a, b)
    summary = []
    for p in ps:
        t0 = time.time()
        res = run(a, b, p, q, workers)
        # re-verify top entries exactly in Python
        for e, m in res[:6]:
            assert energy(mask_to_X(m, a, b), p, q, a, b) == e, (p, m, e)
        estar = energy(mask_to_X(star, a, b), p, q, a, b)
        best_e, best_m = res[0]
        unique = best_m == star and (len(res) < 2 or res[1][0] < best_e)
        info = dict(a=a, b=b, p=p, q=q, star_mask=star, star_energy=estar, best=res[0], second=res[1] if len(res) > 1 else None,
                    star_is_unique_max=unique, gap=(best_e - res[1][0]) if unique else None, top=res[:6],
                    seconds=round(time.time() - t0, 2))
        summary.append(info)
        print(json.dumps(info))
        if not unique:
            for e, m in res[:4]:
                X = mask_to_X(m, a, b)
                print('  mask', m, 'E', e, 'X rows (p-exp i, q-exp j):', X)
