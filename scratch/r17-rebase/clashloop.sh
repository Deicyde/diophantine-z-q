#!/bin/bash
# Iterate: compile AllContrib2.lean (tops minus dropped); on "environment already contains 'X' from Y",
# drop every top whose closure contains Y unless it is the new module; stop on success or on a clash
# whose Y-tops include the new module. One Lean process at a time.
cp scratch/r17-rebase/contrib-tops.txt scratch/r17-rebase/tops-kept.txt
: > scratch/r17-rebase/tops-dropped.txt
for it in $(seq 1 15); do
  { sed 's/^/import /' scratch/r17-rebase/tops-kept.txt; echo; echo "#print axioms CarayolPrinted.carayolR17'_of_printedIrr"; } > scratch/r17-rebase/AllContrib2.lean
  out=$(lake env lean scratch/r17-rebase/AllContrib2.lean 2>&1)
  err=$(echo "$out" | grep -m1 "already contains")
  if [ -z "$err" ]; then echo "ITER $it RESULT:"; echo "$out" | head -5; break; fi
  y=$(echo "$err" | sed -E "s/.* from ([^ ]+).*/\1/")
  echo "ITER $it CLASH: $err"
  python3 scratch/r17-rebase/closure.py scratch/r17-rebase/tops-kept.txt "$y" > /tmp/r17drop.txt
  echo "  tops containing $y: $(tr '\n' ' ' < /tmp/r17drop.txt)"
  if grep -q CarayolPrintedIrr /tmp/r17drop.txt; then echo "  involves the new module; stop"; break; fi
  cat /tmp/r17drop.txt >> scratch/r17-rebase/tops-dropped.txt
  grep -vxF -f /tmp/r17drop.txt scratch/r17-rebase/tops-kept.txt > /tmp/r17kept.txt; mv /tmp/r17kept.txt scratch/r17-rebase/tops-kept.txt
done
