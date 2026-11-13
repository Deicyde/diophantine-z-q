#!/bin/bash
# compile olean/$1 (default Tail.lean) against FSPrefix.olean (one Lean process)
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=$PWD/scratch/g0-fibresimple/olean
F=${1:-Tail.lean}
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
lake env bash -c "LEAN_PATH=$D:\$LEAN_PATH lean $D/$F" > $D/tail_out.txt 2>&1
echo "exit $? in $(( $(date +%s) - start ))s"
grep -vE "^\s*$" $D/tail_out.txt | head -60
