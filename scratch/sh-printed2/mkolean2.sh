#!/bin/bash
# Compile PartB + PartS (over ShRG.olean) to ShP.olean in scratch/sh-printed2/olean (one Lean process).
cd "$(dirname "$0")/../.."
D=$PWD/scratch/sh-printed2/olean
{ echo "import ShRG"; for f in PartB PartS; do grep -v '^import\|^#print' scratch/sh-printed2/$f.lean; echo; done; } > $D/ShP.lean
start=$(date +%s)
LEAN_PATH=$D:$(cat /tmp/shp2_lp.txt) ~/.elan/bin/lean -o $D/ShP.olean -i $D/ShP.ilean $D/ShP.lean 2>&1 | grep -E "error" | head
echo "exit ${PIPESTATUS[0]} in $(( $(date +%s)-start ))s"
