#!/bin/bash
# chk.sh FILE: compile one scratch file with lake env lean (one Lean process), output to run_FILE.txt
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
f=$1; b=$(basename $f .lean)
uptime; free -g | sed -n 2p
timeout 2400 lake env lean $f > scratch/image-plane/run_$b.txt 2>&1
echo "exit $?"; grep -c "error" scratch/image-plane/run_$b.txt
