"""Referee-3 helper: run one command, save its stdout+stderr to a log file, and append the CPU time it used
(user + sys of the child, from getrusage) to logs/cpu_ledger.tsv, so that the total CPU budget can be audited.

Usage: python3 run_timed.py LABEL LOGFILE CWD -- cmd args...
"""
import os, resource, subprocess, sys, time

label, logfile, cwd = sys.argv[1], sys.argv[2], sys.argv[3]
assert sys.argv[4] == '--'
cmd = sys.argv[5:]
here = os.path.dirname(os.path.abspath(__file__))
env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1', MKL_NUM_THREADS='1', VECLIB_MAXIMUM_THREADS='1', NUMEXPR_NUM_THREADS='1')    # never write __pycache__ into the authors' / referee-2 folders
r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
t0 = time.time()
start = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
with open(logfile, 'w') as f:
    f.write(f'# {label}  started {start}  cwd={cwd}\n# cmd: {" ".join(cmd)}\n')
    f.flush()
    rc = subprocess.call(cmd, cwd=cwd, stdout=f, stderr=subprocess.STDOUT, env=env)
r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
cpu = (r1.ru_utime - r0.ru_utime) + (r1.ru_stime - r0.ru_stime)
wall = time.time() - t0
with open(logfile, 'a') as f:
    f.write(f'# exit code {rc}; cpu {cpu:.1f}s; wall {wall:.1f}s; finished {time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}\n')
with open(os.path.join(here, 'logs', 'cpu_ledger.tsv'), 'a') as f:
    f.write(f'{start}\t{label}\t{rc}\t{cpu:.1f}\t{wall:.1f}\n')
print(f'{label}: exit {rc}, cpu {cpu:.1f}s, wall {wall:.1f}s')
sys.exit(rc)
