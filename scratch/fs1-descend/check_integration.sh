#!/bin/bash
# Assemble .checks/Integration.lean = scratch/g0-fibresimple/FibreSimple.lean (verbatim)
# + FiniteDescends.lean (minus its import line) + IntegrationTail.lean, and compile it (one Lean process).
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=scratch/fs1-descend/.checks
mkdir -p $D
{ cat scratch/g0-fibresimple/FibreSimple.lean; echo; tail -n +2 scratch/fs1-descend/FiniteDescends.lean;
  cat scratch/fs1-descend/IntegrationTail.lean; } > $D/Integration.lean
wc -l $D/Integration.lean
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
lake env lean $D/Integration.lean > $D/out.txt 2>&1
echo "exit $? in $(( $(date +%s) - start ))s"
grep -E "error|sorry|fs1|finiteDescends|fibreSimple_of_leaves_fs5|FS1Descend" $D/out.txt | head -30
