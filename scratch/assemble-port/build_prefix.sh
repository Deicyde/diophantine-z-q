#!/bin/bash
# Compile olean/LPrefix.lean (= scratch/assemble-port/LeavesP.lean, made by mk/mk_prefix.py) to an olean (one Lean process)
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=$PWD/scratch/assemble-port/olean
cp scratch/assemble-port/LeavesP.lean $D/LPrefix.lean
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
lake env lean -o $D/LPrefix.olean -i $D/LPrefix.ilean $D/LPrefix.lean > $D/prefix_out.txt 2>&1
echo "exit $? in $(( $(date +%s) - start ))s"
grep -E "error" $D/prefix_out.txt | head -20
