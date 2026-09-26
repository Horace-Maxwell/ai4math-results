#!/bin/zsh
# run each line of the job file (args for runjob3.sh) when fewer than 4 referee compute processes are running
R=${0:A:h:h}   # the review/ folder: this script lives in review/code/
cnt() { pgrep -f "review/code/(sunC [0-9]|sunC2 [0-9]|A4_dump [0-9]|B2v1_dump [0-9])" | wc -l | tr -d ' ' }
while read -r line; do
  while [ $(cnt) -ge 4 ]; do sleep 10; done
  echo "launch $line $(date -u +%H:%M:%S)"
  ${=:-} $R/code/runjob3.sh ${=line} &
  sleep 3
done < $1
wait
echo "sched done $(date -u +%H:%M:%S)"
