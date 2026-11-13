#!/bin/bash
# Compile olean/LPrefix.lean (= Leaves.lean, a verbatim copy of scratch/h-decomposition/Leaves.lean,
# with the three non-HDecomp kernel imports of imports_extra.txt added after its imports) to an olean.
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=$PWD/scratch/linked-tate/olean
S=scratch/linked-tate
{ sed -n 1,3p $S/Leaves.lean; cat $S/imports_extra.txt; sed -n '4,$p' $S/Leaves.lean; } > $D/LPrefix.lean
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
lake env lean -o $D/LPrefix.olean -i $D/LPrefix.ilean $D/LPrefix.lean > $D/prefix_out.txt 2>&1
echo "exit $? in $(( $(date +%s) - start ))s"
grep -E "error" $D/prefix_out.txt | head -20
