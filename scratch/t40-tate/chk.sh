#!/bin/bash
# usage: chk.sh FILE  -- check load, then lake env lean FILE
cd ~/dzq-wt/t40-tate
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
L=$(cut -d' ' -f1 /proc/loadavg); A=$(free -g | awk '/Mem:/{print $7}')
echo "load $L avail ${A}G"
if (( $(echo "$L > 150" | bc) )) || (( A < 20 )); then echo BLOCKED; exit 3; fi
timeout ${T:-1500} lake env lean "$1" 2>&1 | grep -v "^warning\|linter\|^Note: This linter\|set_option linter" | head -${H:-60}
