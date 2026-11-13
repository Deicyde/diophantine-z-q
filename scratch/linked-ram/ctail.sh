#!/bin/bash
# compile olean/$1 against the oleans in scratch/linked-ram/olean (one Lean process); $2 = module name to write an olean
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=$PWD/scratch/linked-ram/olean
F=${1:-Tail.lean}
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
if [ -n "$2" ]; then OUT="-o $D/$2.olean -i $D/$2.ilean"; else OUT=""; fi
lake env bash -c "LEAN_PATH=$D:\$LEAN_PATH lean $OUT $D/$F" > $D/${F%.lean}_out.txt 2>&1
echo "exit $? in $(( $(date +%s) - start ))s"
echo "errors: $(grep -c ': error' $D/${F%.lean}_out.txt)  sorry: $(grep -c "declaration uses 'sorry'" $D/${F%.lean}_out.txt)"
grep -A12 ": error" $D/${F%.lean}_out.txt | head -${3:-80}
echo "--- nonstandard axiom lines:"
grep "depends on axioms" $D/${F%.lean}_out.txt | grep -v "\[propext, Classical.choice, Quot.sound\]" | head
