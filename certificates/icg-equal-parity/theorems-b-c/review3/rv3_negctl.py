"""Referee-3 negative controls for rv3_certify.py (each run MUST report failures):
  NC1  --need 1001/1000 : target d_a d_b - 2(1.001) delta_a delta_b, which Y^- and Y^+ violate; g_+ is then an ordinary last
                          column, and the certificate must fail, at least at the items of g_+ (the column of Y^+).
  NC2  --need 5/4       : a clearly false target.
  NC3  --bpar 1-a%2     : b of the other parity (a + b odd), where the checkerboard s_a s_b^T is admissible and G = d_a d_b > Theta.
  NC4  --regions E33    : p = q = 3 (not a pair of distinct primes; other matrices attain the target there for small shapes).
  NC5  --regions EQ2    : p >= 5, q >= 2 (P_min = 1 < 2).
Usage: python3 rv3_negctl.py a [a ...]
"""
import re, subprocess, sys, os

here = os.path.dirname(os.path.abspath(__file__))
controls = [('NC1 need=1001/1000', ['--need', '1001/1000']),
            ('NC2 need=5/4', ['--need', '5/4']),
            ('NC3 wrong parity of b', ['--bpar', None]),
            ('NC4 region p=q=3', ['--regions', 'E33']),
            ('NC5 region q>=2', ['--regions', 'EQ2'])]
which = sys.argv[1:]
allok = True
for a in [int(x) for x in which if x.isdigit()]:
    for name, fl in controls:
        if name.startswith('NC2') and a > 6:
            continue
        if name.startswith('NC5') and a > 7:
            continue
        fl = list(fl)
        if fl[1] is None:
            fl[1] = str(1 - a % 2)
        cmd = [sys.executable, os.path.join(here, 'rv3_certify.py'), str(a), '--val', '0.02', '--maxfail', '400'] + fl
        out = subprocess.run(cmd, capture_output=True, text=True).stdout
        m = re.search(r'FAILURES: (\d+)', out)
        nf = int(m.group(1)) if m else -1
        fl_lines = [l for l in out.splitlines() if l.strip().startswith('FAIL (')]
        cats = {}
        for l in fl_lines:
            c = l.split("('")[1].split("'")[0] if "('" in l else '?'
            cats[c] = cats.get(c, 0) + 1
        ok = nf > 0
        allok &= ok
        print(f'a={a} {name}: failures {nf} ({"as required" if ok else "NO FAILURE: control did not fire"}); '
              f'by category (first 400 listed): {cats}', flush=True)
        for l in fl_lines[:6]:
            print('      ', l.strip()[:260], flush=True)
        if name.startswith('NC1'):
            gp = [((-1) ** a) * (-1) ** i for i in range(a + 1)]
            gp[a] -= 2
            gp = tuple(gp)
            only_gplus = all(f'g={gp}' in l or 'Delta(g_+)' in l for l in fl_lines)
            print(f'      NC1: all listed failures concern g_+ = {gp} (or the identity Delta(g_+) = 2 delta): {only_gplus}',
                  flush=True)
        if name.startswith('NC3'):
            s_b = tuple(((-1) ** (1 - a % 2)) * (-1) ** i for i in range(a + 1))
            hit = any(f'C3' in l and f'g={s_b}' in l for l in fl_lines)
            print(f'      NC3: the full-chain condition (C3) fails for g = (-1)^b s_a = {s_b}: {hit}', flush=True)
print('ALL NEGATIVE CONTROLS FIRED' if allok else 'SOME NEGATIVE CONTROL DID NOT FIRE')
