#!/bin/bash
# PGAll.lean = import PGBase + BCU, QMTwist, PiTwist, S8, W8, SFA (import and #print lines removed)
# + final_part.lean (the end-to-end theorem). Run from the repository root after build_base.sh.
set -e
D=scratch/period-glue
{ echo "import PGBase"
  for f in BCU QMTwist PiTwist S8 W8 SFA; do sed '/^import /d; /^#print axioms/d' $D/$f.lean; done
  cat $D/final_part.lean; } > $D/PGAll.lean
LEAN_PATH=$(lake env printenv LEAN_PATH):$D/olean lean $D/PGAll.lean
