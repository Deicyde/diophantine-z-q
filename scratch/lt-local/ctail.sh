#!/bin/bash
# compile scratch/lt-local/$1 against olean/ (one Lean process); optional $2 = olean name to write
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=$PWD/scratch/lt-local
F=${1:-Part.lean}
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
if [ -n "$2" ]; then OUT="-o $D/olean/$2.olean -i $D/olean/$2.ilean"; else OUT=""; fi
lake env bash -c "LEAN_PATH=$D/olean:\$LEAN_PATH lean $OUT $D/$F" > $D/${F%.lean}.out 2>&1
echo "exit $? in $(( $(date +%s) - start ))s"
grep -E "error|sorry" $D/${F%.lean}.out | head -${3:-40}; grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" $D/${F%.lean}.out
