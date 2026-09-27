#!/bin/zsh
# Run implementation B for n=19..24, 3 shards each (3 cores), sequentially in n.
W=${0:A:h:h}
cd $W/code
for n in 19 20 21 22 23 24; do
  echo "start n=$n $(date -u +%Y-%m-%dT%H:%M:%SZ)" >> $W/logs/swtrees_B.log
  for r in 0 1 2; do ./swtrees $n 3 $r > $W/logs/swtrees_B_n${n}_s${r}.out & done
  wait
  echo "end n=$n $(date -u +%Y-%m-%dT%H:%M:%SZ)" >> $W/logs/swtrees_B.log
  cat $W/logs/swtrees_B_n${n}_s*.out >> $W/logs/swtrees_B.log
done
