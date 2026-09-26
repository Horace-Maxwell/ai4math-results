#!/bin/sh
# Re-run every referee check (exact arithmetic; Python 3.12, sympy 1.13, numpy 1.26). Total runtime ~5 minutes.
set -e
cd "$(dirname "$0")"
mkdir -p logs
for s in rv_prop1 rv_lemmaS rv_states rv_fd_forms rv_fd_cert rv_fd_true rv_hand rv_eq_cases rv_brute rv_graph rv_search; do
  echo "== $s"
  python3 "$s.py" > "logs/$s.log" 2>&1
  tail -1 "logs/$s.log"
done
