#!/bin/zsh
# args: kind b N part nparts
R=${0:A:h:h}   # the review/ folder: this script lives in review/code/
case $1 in
  A)  f=$R/logs/Adump_b$2_N$3_p$4of$5; echo "start $(date -u +%H:%M:%S)" > $f.err; $R/code/A_dump $2 $3 $4 $5 > $f.out 2>> $f.err ;;
  B2) f=$R/logs/B2dump_b$2_N$3_p$4of$5; echo "start $(date -u +%H:%M:%S)" > $f.err; $R/code/B2_dump $2 $3 $4 $5 > $f.out 2>> $f.err ;;
  C)  f=$R/logs/C_b$2_N$3_noprune_p$4of$5; echo "start $(date -u +%H:%M:%S)" > $f.err; $R/code/sunC $2 $3 noprune 1 $4 $5 > $f.out 2>> $f.err ;;
  A4) f=$R/logs/A4dump_b$2_N$3_p$4of$5; echo "start $(date -u +%H:%M:%S)" > $f.err; $R/code/A4_dump $2 $3 $4 $5 > $f.out 2>> $f.err ;;
  B2v1) f=$R/logs/B2v1dump_b$2_N$3_p$4of$5; echo "start $(date -u +%H:%M:%S)" > $f.err; $R/code/B2v1_dump $2 $3 $4 $5 > $f.out 2>> $f.err ;;
  C2) f=$R/logs/C2_b$2_N$3_prune2_p$4of$5; echo "start $(date -u +%H:%M:%S)" > $f.err; $R/code/sunC2 $2 $3 prune2 1 $4 $5 > $f.out 2>> $f.err ;;
  CP) f=$R/logs/C_b$2_N$3_prune_p$4of$5; echo "start $(date -u +%H:%M:%S)" > $f.err; $R/code/sunC $2 $3 prune 1 $4 $5 > $f.out 2>> $f.err ;;
esac
echo "end $(date -u +%H:%M:%S)" >> $f.err
