#!/bin/bash
# leaf-fold6: compile a chain source against the oleans in scratch/leaf-fold6/olean (one Lean process).
# $1 = source file (relative to the repository root), $2 = module name to write an olean (optional), $3 = lines of errors shown
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=$PWD/scratch/leaf-fold6/olean
F=$1
B=$(basename ${F%.lean})
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
if [ -n "$2" ]; then OUT="-o $D/$2.olean -i $D/$2.ilean"; else OUT=""; fi
lake env bash -c "LEAN_PATH=$D:\$LEAN_PATH lean $OUT $PWD/$F" > $D/${B}_out.txt 2>&1
echo "exit $? in $(( $(date +%s) - start ))s"
echo "errors: $(grep -c ': error' $D/${B}_out.txt)  sorry: $(grep -c "declaration uses 'sorry'" $D/${B}_out.txt)"
grep -A6 ": error" $D/${B}_out.txt | head -${3:-80}
echo "--- nonstandard axiom lines:"
grep "depends on axioms" $D/${B}_out.txt | grep -v "\[propext, Classical.choice, Quot.sound\]" | head
