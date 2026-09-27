#!/bin/zsh
# After the NT=5 region search finishes, run the independent re-check (region_indep.py) for NT = 2, 3, 4 on 4 cores.
W=${0:A:h:h}
until ! pgrep -f "region_search.py 5" >/dev/null; do sleep 20; done
cd $W/code
echo "start indep $(date -u +%H:%M:%SZ)" > $W/s3/indep_run.log
python3 region_indep.py 2 1 0 > $W/s3/indep_NT2.log 2>&1
python3 region_indep.py 3 1 0 > $W/s3/indep_NT3.log 2>&1
for r in 0 1 2 3; do python3 region_indep.py 4 4 $r > $W/s3/indep_NT4_s$r.log 2>&1 & done
wait
echo "end indep $(date -u +%H:%M:%SZ)" >> $W/s3/indep_run.log
