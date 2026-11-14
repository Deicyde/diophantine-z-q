#!/bin/bash
# leaf-fold6: compile the olean chain in order (one Lean process at a time), stopping at the first failure.
# LPrefix ... TailK: leaf-fold4's committed sources scratch/leaf-fold4/olean/*.lean; TailL, TailM, TailN: leaf-fold5's
# scratch/leaf-fold5/olean/*.lean; TailO: this task's scratch/leaf-fold6/olean/TailO.lean (assemble.sh). All compiled
# unchanged, oleans written to scratch/leaf-fold6/olean (not committed).
# Usage: ./chain.sh [first-module] [last-module]
cd "$(dirname "$0")"
OLD4="LPrefix TailA TailB TailC TailD LF2Stalks LF2UnifRoot LF2SmoothDim LF2UnramConj LF3Cot TailE TailF TailG TailH TailI LF4T5 TailJ TailK"
OLD5="TailL TailM TailN"
NEW="TailO"
start=${1:-LPrefix}; stop=${2:-NONE}; go=0
for m in $OLD4 $OLD5 $NEW; do
  [ "$m" = "$start" ] && go=1
  [ $go = 1 ] || continue
  if echo " $OLD4 " | grep -q " $m "; then src=scratch/leaf-fold4/olean/$m.lean
  elif echo " $OLD5 " | grep -q " $m "; then src=scratch/leaf-fold5/olean/$m.lean
  else src=scratch/leaf-fold6/olean/$m.lean; fi
  echo "== $m $(date +%H:%M:%S)"
  ./ctail.sh $src $m 40 || exit 1
  e=$(grep -c ': error' olean/${m}_out.txt)
  if [ "$e" != "0" ]; then echo "STOP at $m ($e errors)"; exit 1; fi
  [ "$m" = "$stop" ] && break
done
echo "CHAIN DONE $(date +%H:%M:%S)"
