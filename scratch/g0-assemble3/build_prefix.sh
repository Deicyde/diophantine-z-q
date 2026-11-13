#!/bin/bash
# Compile olean/LPrefix.lean (= scratch/g0-assemble3/Leaves.lean, copied verbatim) to an olean (one Lean process)
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=$PWD/scratch/g0-assemble3/olean
cp scratch/g0-assemble3/Leaves.lean $D/LPrefix.lean
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
lake env lean -o $D/LPrefix.olean -i $D/LPrefix.ilean $D/LPrefix.lean > $D/prefix_out.txt 2>&1
echo "exit $? in $(( $(date +%s) - start ))s"
grep -E "error" $D/prefix_out.txt | head -20
