# Compare the b=10, N=41 moment-feasible leaf sets of A (A_dump) and B2 (B2_dump) as SETS, then
# re-test every leaf of the union with the referee's exact test (sunC_batch: Schwenk charpoly mod 2 primes).
import glob, os, subprocess, sys, collections
R = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')   # the review/ folder
def load(pattern):
    S = collections.Counter()
    for fn in sorted(glob.glob(R + '/logs/' + pattern)):
        for line in open(fn):
            if line.startswith('LEAF'):
                S[tuple(tuple(map(int, t.split(','))) for t in line.split()[1:])] += 1
    return S
A = load('A4dump_b10_N41_p*of2.out'); B = load('B2v1dump_b10_N41_p*of4.out')
print('A leaves (with multiplicity):', sum(A.values()), 'distinct:', len(A), 'max dup:', max(A.values()) if A else 0)
print('B2 leaves (with multiplicity):', sum(B.values()), 'distinct:', len(B), 'max dup:', max(B.values()) if B else 0)
a, b = set(A), set(B)
print('A == B2 as sets:', a == b, '| only A:', len(a - b), '| only B2:', len(b - a))
for t in list(a - b)[:5]: print('  only A :', t)
for t in list(b - a)[:5]: print('  only B2:', t)
U = sorted(a | b)
inp = ''.join('10 ' + ' '.join('%d %d' % pq for pq in t) + '\n' for t in U)
out = subprocess.run([R + '/code/sunC_batch', 'batch'], input=inp, capture_output=True, text=True).stdout.split('\n')
integral = [U[i] for i, l in enumerate(out[:len(U)]) if l and len(set(l.split())) == 1]
nq = sum(1 for t in U if any(q for _, q in t))
print('union size', len(U), '| containing a P2:', nq, '| referee exact test: integral =', len(integral))
# check the rotation filter (v0 carries the maximal key p*1000+q) holds for every leaf
bad = [t for t in U if any(p*1000+q > t[0][0]*1000+t[0][1] for p, q in t)]
print('leaves violating the v0-max-key rotation filter:', len(bad))
