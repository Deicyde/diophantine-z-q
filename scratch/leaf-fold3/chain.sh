#!/bin/bash
# leaf-fold3: compile the olean chain in order (one Lean process at a time), stopping at the first failure.
# Usage: ./chain.sh [first-module]   (modules: LPrefix TailA TailB TailC TailD LF2Stalks LF2UnifRoot LF2SmoothDim LF2UnramConj LF3Cot TailE TailF TailG TailH TailI)
cd "$(dirname "$0")"
MODS="LPrefix TailA TailB TailC TailD LF2Stalks LF2UnifRoot LF2SmoothDim LF2UnramConj LF3Cot TailE TailF TailG TailH TailI"
start=${1:-LPrefix}; go=0
for m in $MODS; do
  [ "$m" = "$start" ] && go=1
  [ $go = 1 ] || continue
  echo "== $m $(date +%H:%M:%S)"
  ./ctail.sh $m.lean $m 40 || exit 1
  e=$(grep -c ': error' olean/${m}_out.txt)
  if [ "$e" != "0" ]; then echo "STOP at $m ($e errors)"; exit 1; fi
done
echo "CHAIN DONE $(date +%H:%M:%S)"
