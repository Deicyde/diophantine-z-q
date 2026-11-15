#!/bin/bash
# usage: chk.sh file.lean  -- compiles against qmrec-printed's build tree (read-only), one Lean process
L=$(cut -d' ' -f1 /proc/loadavg); A=$(free -g | awk '/Mem:/{print $7}')
echo "load=$L avail=${A}G"
if (( $(echo "$L > 150" | bc) )) || (( A < 20 )); then echo BLOCKED; exit 2; fi
Q=/home/jackmccarthy/dzq-wt/qmrec-printed
export LEAN_PATH=$Q/.lake/packages/Cli/.lake/build/lib/lean:$Q/.lake/packages/batteries/.lake/build/lib/lean:$Q/.lake/packages/Qq/.lake/build/lib/lean:$Q/.lake/packages/aesop/.lake/build/lib/lean:$Q/.lake/packages/proofwidgets/.lake/build/lib/lean:$Q/.lake/packages/importGraph/.lake/build/lib/lean:$Q/.lake/packages/LeanSearchClient/.lake/build/lib/lean:$Q/.lake/packages/plausible/.lake/build/lib/lean:$Q/.lake/packages/mathlib/.lake/build/lib/lean:$Q/lean/.lake/build/lib/lean:$Q/.lake/build/lib/lean
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
/usr/bin/time -f "time %e s, maxrss %M KB" lean "$@"
