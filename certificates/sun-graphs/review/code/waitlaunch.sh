#!/bin/zsh
# wait until fewer than 1 of my sunC jobs remain, then launch queue 3 with 4 workers
R=${0:A:h:h}   # the review/ folder: this script lives in review/code/
while [ $(pgrep -f "review/code/sunC [0-9]" | wc -l) -gt 0 ]; do sleep 20; done
cd $R/code && cat jobs3.txt | xargs -P 4 -L 1 ./runjob3.sh
echo "queue3 done $(date -u +%H:%M:%S)"
