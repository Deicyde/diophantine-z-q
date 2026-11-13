#!/bin/bash
# Compile olean/LPrefix.lean to an olean. LPrefix.lean = scratch/linked-tate/Leaves.lean (linked-tate's
# verbatim copy of the pin-applied scratch/h-decomposition/Leaves.lean) with linked-tate's three extra
# kernel imports, exactly as scratch/linked-tate/build_prefix.sh builds it. (one Lean process)
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=$PWD/scratch/hom-unify/olean
S=scratch/linked-tate
{ sed -n 1,3p $S/Leaves.lean; cat $S/imports_extra.txt; sed -n '4,$p' $S/Leaves.lean; } > $D/LPrefix.lean
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
lake env lean -o $D/LPrefix.olean -i $D/LPrefix.ilean $D/LPrefix.lean > $D/prefix_out.txt 2>&1
echo "exit $? in $(( $(date +%s) - start ))s"
grep -E "error" $D/prefix_out.txt | head -20
