#!/bin/bash
# run the Tail modules in order (one Lean process at a time), stop at the first that has errors
cd "$(dirname "$0")"
for M in ${@:-TailA TailB TailC TailE TailF TailD}; do
  echo "== $M"; bash ctail.sh $M.lean $M 2>&1 | head -40
  grep -q ': error' olean/${M}_out.txt && { echo "STOP at $M"; exit 1; }
done
echo ALLDONE
