#!/bin/bash
# Check a leafq-check file that imports leaf-fold4's olean chain (TailK etc.).
# Needs leaf-fold4's compiled chain (scratch/leaf-fold4/chain.sh) copied to $OL and leaf-fold4's lake build
# (LEAN_PATH of `lake env` in that worktree, saved in $OL/LEAN_PATH.txt). One Lean process.
OL=${OL:-$HOME/lqc-olean}
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
LEAN_PATH=$OL:$(cat $OL/LEAN_PATH.txt) lean "$@"
echo "exit $? in $(( $(date +%s) - start ))s"
