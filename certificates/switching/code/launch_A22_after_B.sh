#!/bin/zsh
# Wait until implementation B has finished n=24, then run A' (networkx generator + exact checker) for n=22 on 3 shards.
W=${0:A:h:h}
until grep -q "^end n=24" $W/logs/swtrees_B.log; do sleep 20; done
echo "B finished n=24 at $(date -u +%Y-%m-%dT%H:%M:%SZ); launching A' n=22" >> $W/logs/launch_A22.log
cd $W/code
for r in 0 1 2; do OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 python3 swtrees_A_nx.py 22 3 $r > $W/logs/swtrees_Anx_n22_s$r.log 2>&1 & done
wait
echo "A' n=22 finished at $(date -u +%Y-%m-%dT%H:%M:%SZ)" >> $W/logs/launch_A22.log
