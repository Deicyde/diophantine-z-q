#!/bin/bash
# usage: bld.sh MODULE...  -- check load, then lake build, print errors
cd ~/dzq-wt/t40-tate
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
L=$(cut -d' ' -f1 /proc/loadavg); A=$(free -g | awk '/Mem:/{print $7}')
echo "load $L avail ${A}G"
if (( $(echo "$L > 150" | bc) )) || (( A < 20 )); then echo BLOCKED; exit 3; fi
timeout ${T:-3000} lake build "$@" > /tmp/t40-bld.txt 2>&1; echo "exit $?"
grep -E "^error|✖|^  |^⊢" /tmp/t40-bld.txt | grep -v "^error: build failed" | head -${H:-80}
