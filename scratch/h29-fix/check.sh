#!/bin/sh
# h29-fix: regenerate DischargesH29Fix.lean (header of the contribution + Main + Discharges, the contribution body
# verbatim, then the tail block kept in check-tail.lean) and compile it (one Lean process).
set -e
cd "$(dirname "$0")/../.."
F=scratch/h29-fix/TYZLemma29Mod2.lean
{ echo "import ZInQKernel.OneProof.Main"; echo "import ZInQKernel.OneProof.Discharges"; sed -n '1,3p' $F; echo
  echo "/-! Check file (h29-fix): the revised contribution verbatim (generated from scratch/h29-fix/TYZLemma29Mod2.lean by check.sh), then axioms, Theorem 1.1 with h29 replaced, and #discharges. -/"
  sed -n '4,$p' $F; cat scratch/h29-fix/check-tail.lean; } > scratch/h29-fix/DischargesH29Fix.lean
lake env lean scratch/h29-fix/DischargesH29Fix.lean > scratch/h29-fix/DischargesH29Fix-output.txt 2>&1
