#!/bin/bash
# Check a qm-split file that imports leaf-fold4's olean chain (TailK etc.), copied to $OL
# (from leafq-check's ~/lqc-olean; LEAN_PATH of leaf-fold4's lake build in $OL/LEAN_PATH.txt). One Lean process.
OL=${OL:-$HOME/qms-olean}
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
LEAN_PATH=$OL:$(cat $OL/LEAN_PATH.txt) lean "$@"
echo "exit $? in $(( $(date +%s) - start ))s"
