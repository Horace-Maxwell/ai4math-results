import sys
from general_a import fd1, cheap
from general_chain import run as chain_run
for a in [5, 6]:
    bs = [b for b in range(1, 9) if (a + b) % 2 == 0]
    for (p, q) in [(5, 3), (3, 5), (7, 3), (3, 7), (5, 7)]:
        w = fd1(a, p, q, bs)
        print(f"a={a} p={p} q={q}: FD1_a min ratio {float(w[0]):.4f} at b={w[1]} J={w[2]} dev={w[3]}{'   <-- FAILS' if w[0] <= 1 else ''}")
        sys.stdout.flush()
    for (p, q) in [(5, 3), (3, 5)]:
        chain_run(a, p, q, [b for b in range(1, 7) if (a + b) % 2 == 0])
