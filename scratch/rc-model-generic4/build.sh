#!/bin/bash
# usage: build.sh Module.Name  (one Lean process at a time)
read l1 _ < /proc/loadavg
avail=$(free -g | awk '/Mem:/{print $7}')
echo "load=$l1 avail=${avail}G"
if (( ${l1%.*} > 120 )) || (( avail < 20 )); then echo "BLOCKED by host thresholds"; exit 3; fi
cd /home/jackmccarthy/dzq-wt/rc-model-generic4
OUT=/tmp/rcmg4-build.out
LEAN_NUM_THREADS=4 timeout ${TMO:-3000} systemd-run --user --scope -q -p CPUQuota=1600% -p MemoryMax=60G nice lake build "$@" > $OUT 2>&1
rc=$?
awk '
/^(warning|error|info|⚠|✖|✔|trace)/ { show = 0 }
/^error/ { show = 1 }
/^(warning|info): ZInQKernel\/Contrib\/OneProof\/RC\/ModelGeneric4/ { show = 1 }

show { print }
' $OUT | grep -v "linter\|Try this\|letI̵\|haveI̵\|preferred over\|difference between\|not relevant for proofs" | head -${LINES_OUT:-100}
grep -E "^(✖|error: build failed|Build completed)" $OUT | tail -3
echo "exit=$rc"
