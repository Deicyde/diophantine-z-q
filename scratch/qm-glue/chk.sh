#!/bin/bash
# Check a qm-glue file that imports the leaf-fold4 olean chain (TailK etc.). The chain oleans (compiled by
# leaf-fold6 from leaf-fold4's committed sources), the kernel module oleans and the z_in_q oleans are copied to
# $OL (from ~/dzq-wt/leaf-fold6: scratch/leaf-fold6/olean, .lake/build/lib/lean, lean/.lake/build/lib/lean).
# One Lean process. Self-contained files (import Mathlib) are checked with `lake env lean` instead.
OL=${OL:-$HOME/qmg-olean}
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")/../.."
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
lake env bash -c "LEAN_PATH=$OL/chain:$OL/kern:$OL/zinq:\$LEAN_PATH lean $*"
echo "exit $? in $(( $(date +%s) - start ))s"
