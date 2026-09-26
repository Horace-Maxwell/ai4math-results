"""Independent exact integer recurrence check; not a proof of the universal claim."""
import datetime, hashlib, json, math, time
from pathlib import Path
out = Path(__file__).parent
start = time.monotonic()
N = 1000
a = [0, 1, 1] + [0] * (N - 2)
for n in range(3, N+1):
    a[n] = sum(a[k] * math.comb(k, n+2-2*k)
               for k in range((n+2)//2+1) if 0 <= n+2-2*k <= k)
b = [tuple(map(int, line.split())) for line in (out/'b389472.txt').read_text().splitlines()
     if line.strip() and not line.startswith('#')]
report = {
 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'algorithm': 'integer coefficient recursion extracted from A(X^2+X^3)=X^2(1+A)',
 'range': [0,N], 'seed': [0,1,1],
 'bfile_rows': len(b), 'bfile_mismatches': [n for n,x in b if n <= N and a[n] != x],
 'mod3_indices_checked': sum(1 for n in range(3,N+1) if n%3 == 2),
 'mod3_counterexamples': [n for n in range(3,N+1) if n%3 == 2 and a[n]%3 != 0],
 'elapsed_seconds': time.monotonic()-start,
 'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'bfile_sha256': hashlib.sha256((out/'b389472.txt').read_bytes()).hexdigest(),
 'first20_terms': a[1:21],
 'meaning': 'Exact finite independent sanity check; universal proof is separate Lean theorem.'
}
(out/'a389472-experiment.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
