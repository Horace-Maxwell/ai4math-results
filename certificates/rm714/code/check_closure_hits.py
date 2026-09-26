"""check_closure_hits.py -- independent re-check (pure Python) of the F_TRUTH_TABLE_HEX lines printed by
closure_search.c: recompute the weight and the ANF degree of each reported codeword f on F_2^(m+1)."""
import sys
def check(path, m1, rmax):
    L = open(path).read().split('\n'); n = 0; bad = 0; seen = {}
    for i, l in enumerate(L):
        if not l.startswith('F_TRUTH_TABLE_HEX'): continue
        prev = L[i - 1]; target = int(prev.split('target=')[1].split()[0])
        words = [int(x, 16) for x in l.split()[1:]]
        N = 1 << m1
        t = [(words[x >> 6] >> (x & 63)) & 1 for x in range(N)]
        a = t[:]
        for j in range(m1):
            b = 1 << j
            for x in range(N):
                if x & b: a[x] ^= a[x ^ b]
        deg = max(bin(x).count('1') for x in range(N) if a[x])
        wt = sum(t); ok = (wt == target and deg <= rmax)
        n += 1; bad += (not ok); seen[target] = seen.get(target, 0) + 1
    return n, bad, seen
if __name__ == '__main__':
    m1, rmax = int(sys.argv[1]), int(sys.argv[2])
    tot = 0; totbad = 0; allseen = {}
    for p in sys.argv[3:]:
        n, bad, seen = check(p, m1, rmax); tot += n; totbad += bad
        for k, v in seen.items(): allseen[k] = allseen.get(k, 0) + v
    print('rechecked codewords:', tot, 'failures:', totbad, 'by weight:', dict(sorted(allseen.items())))
