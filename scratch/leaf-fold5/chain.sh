#!/bin/bash
# leaf-fold5: compile the olean chain in order (one Lean process at a time), stopping at the first failure.
# Modules LPrefix ... TailK are leaf-fold4's committed sources scratch/leaf-fold4/olean/*.lean, compiled unchanged
# (oleans written here); TailL ... are this task's (scratch/leaf-fold5/olean/*.lean, made by assemble.sh).
# Usage: ./chain.sh [first-module] [last-module]
cd "$(dirname "$0")"
OLD="LPrefix TailA TailB TailC TailD LF2Stalks LF2UnifRoot LF2SmoothDim LF2UnramConj LF3Cot TailE TailF TailG TailH TailI LF4T5 TailJ TailK"
NEW="TailL TailM TailN"
start=${1:-LPrefix}; stop=${2:-NONE}; go=0
for m in $OLD $NEW; do
  [ "$m" = "$start" ] && go=1
  [ $go = 1 ] || continue
  if echo " $OLD " | grep -q " $m "; then src=scratch/leaf-fold4/olean/$m.lean; else src=scratch/leaf-fold5/olean/$m.lean; fi
  echo "== $m $(date +%H:%M:%S)"
  ./ctail.sh $src $m 40 || exit 1
  e=$(grep -c ': error' olean/${m}_out.txt)
  if [ "$e" != "0" ]; then echo "STOP at $m ($e errors)"; exit 1; fi
  [ "$m" = "$stop" ] && break
done
echo "CHAIN DONE $(date +%H:%M:%S)"
