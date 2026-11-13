#!/bin/bash
# Compile olean/LPrefix.lean (= linked-tate's prefix: scratch/linked-tate/Leaves.lean with the imports of
# scratch/linked-frob/imports_extra.txt (linked-tate's three + frob-pieces' Contrib module) after its three imports) to an olean.
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=$PWD/scratch/linked-frob/olean
S=scratch/linked-tate
{ sed -n 1,3p $S/Leaves.lean; cat scratch/linked-frob/imports_extra.txt; sed -n '4,$p' $S/Leaves.lean; } > $D/LPrefix.lean
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
lake env lean -o $D/LPrefix.olean -i $D/LPrefix.ilean $D/LPrefix.lean > $D/prefix_out.txt 2>&1
echo "exit $? in $(( $(date +%s) - start ))s"
grep -E "error" $D/prefix_out.txt | head -20
