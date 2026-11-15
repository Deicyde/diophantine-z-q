#!/bin/bash
# Compile the sh-route prefix (Head + SR_* files) to an olean ShRG.olean in /tmp/shp2-olean (one Lean process).
# Needs /tmp/shp2_lp.txt = `lake env printenv LEAN_PATH` of a built worktree.
cd "$(dirname "$0")/../.."
D=$PWD/scratch/sh-printed2/olean; mkdir -p $D
{ cat scratch/sh-printed2/Head.lean; echo;
  for f in SR_Top SR_CA1 SR_CA2 SR_CA3 SR_Final; do grep -v '^import\|^#print' scratch/sh-printed2/$f.lean; echo; done; } > $D/ShRG.lean
start=$(date +%s)
LEAN_PATH=$D:$(cat /tmp/shp2_lp.txt) ~/.elan/bin/lean -o $D/ShRG.olean -i $D/ShRG.ilean $D/ShRG.lean 2>&1 | grep -E "error" | head
echo "exit ${PIPESTATUS[0]} in $(( $(date +%s)-start ))s"
