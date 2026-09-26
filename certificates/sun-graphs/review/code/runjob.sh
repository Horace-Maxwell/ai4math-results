#!/bin/zsh
# args: b N prune allow3 part nparts
R=${0:A:h:h}   # the review/ folder: this script lives in review/code/
f=$R/logs/C_b$1_N$2_$3_p$5of$6
echo "start $(date -u +%H:%M:%S)" > $f.err
/usr/bin/time -p $R/code/sunC $1 $2 $3 $4 $5 $6 > $f.out 2>> $f.err
echo "end $(date -u +%H:%M:%S)" >> $f.err
