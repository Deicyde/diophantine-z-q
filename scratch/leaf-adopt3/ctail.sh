#!/bin/bash
# compile olean/Tail.lean against HDPrefix.olean (one Lean process)
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=$PWD/scratch/leaf-adopt3/olean
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
lake env bash -c "LEAN_PATH=$D:\$LEAN_PATH lean $D/Tail.lean" > $D/tail_out.txt 2>&1
echo "exit $? in $(( $(date +%s) - start ))s"
grep -E "^[^ ]*: error|error:" $D/tail_out.txt | head -30
grep -c "error" $D/tail_out.txt
