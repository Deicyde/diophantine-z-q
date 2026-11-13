#!/bin/bash
# Compile olean/LPrefix.lean (= scratch/h-decomposition/Leaves.lean, post pin-apply, verbatim) to an olean
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=$PWD/scratch/rv-gluepieces2/olean
cp scratch/h-decomposition/Leaves.lean $D/LPrefix.lean
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
lake env lean -o $D/LPrefix.olean -i $D/LPrefix.ilean $D/LPrefix.lean > $D/prefix_out.txt 2>&1
echo "exit $? in $(( $(date +%s) - start ))s"
grep -E "error" $D/prefix_out.txt | head -20
