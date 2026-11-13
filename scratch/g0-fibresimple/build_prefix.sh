#!/bin/bash
# Compile olean/FSPrefix.lean (= scratch/g0-split/Split.lean, copied) to an olean (one Lean process)
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=$PWD/scratch/g0-fibresimple/olean
cp scratch/g0-split/Split.lean $D/FSPrefix.lean
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
lake env lean -o $D/FSPrefix.olean -i $D/FSPrefix.ilean $D/FSPrefix.lean > $D/prefix_out.txt 2>&1
echo "exit $? in $(( $(date +%s) - start ))s"
grep -E "error" $D/prefix_out.txt | head -20
