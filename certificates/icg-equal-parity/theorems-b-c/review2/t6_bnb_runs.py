"""Referee-2: exact verification of Conjecture 12 (sign-matrix form: max G = Theta, maximisers exactly Y-, Y+) by branch and
bound (bnb.py, validated against brute force in t5_bnb_validate.py) for shapes outside Proposition 13, at fixed parameters.
Lemma S (crude) is verified exactly at each parameter point before the bound is used.  Usage: python3 t6_bnb_runs.py [workers]
"""
import sys, time
from fractions import Fraction as Fr
from multiprocessing import Pool
from bnb import bnb
from r2core import anti, trunc

def job(args):
    a, b, p, q = args
    t0 = time.time()
    try:
        th, res, nodes = bnb(a, b, p, q)
    except AssertionError as e:
        return (a, b, str(p), str(q), 'ERROR ' + str(e)[:80], 0, 0)
    Ys = sorted(tuple(map(tuple, Y)) for g, Y in res)
    ok = (Ys == sorted([tuple(map(tuple, anti(a, b))), tuple(map(tuple, trunc(a, b)))]) and all(g == th for g, Y in res))
    return (a, b, str(p), str(q), 'OK' if ok else f'FAIL {len(res)} {[g - th for g, Y in res][:5]}', nodes, time.time() - t0)

if __name__ == "__main__":
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    pts_int = [(5, 3), (3, 5), (7, 3), (3, 7), (5, 7), (7, 5), (11, 3), (3, 11), (13, 5), (101, 3), (3, 101)]
    pts_rat = [(Fr(11, 2), Fr(7, 2)), (Fr(21, 4), Fr(3)), (Fr(5), Fr(13, 4)), (Fr(3), Fr(21, 4))]
    jobs = []
    for (a, bs) in ((3, [5, 7, 9, 11, 13, 15, 17, 19, 21, 25]), (4, [4, 6, 8, 10, 12, 14, 16, 20]),
                    (5, [3, 5, 7, 9, 11]), (6, [4, 6, 8, 10]), (2, [10, 12, 20])):
        for b in bs:
            for (p, q) in pts_int:
                jobs.append((a, b, Fr(p), Fr(q)))
            if b <= 11:
                for (p, q) in pts_rat:
                    jobs.append((a, b, p, q))
    out = open('logs/t6_bnb_runs.log', 'w')
    t0 = time.time()
    with Pool(workers) as pool:
        for r in pool.imap_unordered(job, jobs):
            line = f"({r[0]},{r[1]}) p={r[2]} q={r[3]}: {r[4]}  nodes={r[5]}  {r[6]:.1f}s"
            out.write(line + '\n'); out.flush()
            if not r[4].startswith('OK'): print(line, flush=True)
    out.write(f"done {len(jobs)} jobs in {time.time()-t0:.0f}s\n")
    print(f"done {len(jobs)} jobs in {time.time()-t0:.0f}s")
