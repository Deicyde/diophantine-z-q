#!/bin/bash
# Check one development file (which does `import ShRG`) against the olean prefix (one Lean process).
cd "$(dirname "$0")/../.."
D=$PWD/scratch/sh-printed2/olean
L=$(uptime | sed 's/.*load average: \([0-9]*\).*/\1/'); M=$(free -g | awk '/Mem/{print $7}')
if [ "$L" -gt 150 ] || [ "$M" -lt 20 ]; then echo "BLOCKED load=$L avail=$M"; exit 1; fi
start=$(date +%s)
LEAN_PATH=$D:$(cat /tmp/shp2_lp.txt) timeout 1500 ~/.elan/bin/lean "$PWD/scratch/sh-printed2/$1" 2>&1 | grep -v "^warning\|linter\|^$\|Note:\|Hint:\|\[apply\]\|binding can be removed\|consider restructuring\|omit \[\|^  \[" 
echo "exit ${PIPESTATUS[0]} in $(( $(date +%s)-start ))s"
