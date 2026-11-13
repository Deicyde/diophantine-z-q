#!/bin/bash
# compile olean/$1 against the oleans in olean/ (one Lean process); $2 = olean name to write
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=$PWD/scratch/hom-unify/olean
F=${1:-Tail.lean}
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
if [ -n "$2" ]; then OUT="-o $D/$2.olean -i $D/$2.ilean"; else OUT=""; fi
lake env bash -c "LEAN_PATH=$D:\$LEAN_PATH lean $OUT $D/$F" > $D/${F%.lean}_out.txt 2>&1
echo "exit $? in $(( $(date +%s) - start ))s"
grep -vE "^\s*$" $D/${F%.lean}_out.txt | grep -v "depends on axioms: \[propext, Classical.choice, Quot.sound\]" | head -60
