#!/bin/bash
# KerWildFix.lean =
#   imports (union of the sources' imports)
# + scratch/local-glue/LocalGlue.lean body (CURRENT source, verbatim; since b582bf03 it contains
#   g0-dim's `G0Dim` block (DimBlock) and `localGlue_of_baseChange'`) + `end` (closes its unclosed
#   top-level `noncomputable section`)
# + scratch/frob-trace/FrobTrace.lean body (verbatim) WITHOUT its lines 1632-1754 (unram-tate's
#   BCPoints block, already in LocalGlue.lean as local-glue's bc_block), in a section
# + scratch/lg-kerwild/part_kerwild.lean, part_tbk.lean, part_final.lean (verbatim, read-only).
#   lg-kerwild's own build.sh also spliced scratch/g0-dim/Dim.lean l.107-305, 339-344: these are now
#   in LocalGlue.lean (diff: identical), so they are NOT spliced again (that was the integration
#   conflict found by rv-fast).
# + part_fix.lean (new, kerwild-fix).
# `#print axioms` lines of the copies are dropped.
cd "$(dirname "$0")"
LG=../local-glue/LocalGlue.lean
FT=../frob-trace/FrobTrace.lean
KW=../lg-kerwild
UR=../unram-roots
{
  cat $LG $FT | grep '^import' | awk '!seen[$0]++'
  echo
  echo "-- BEGIN verbatim body of scratch/local-glue/LocalGlue.lean"
  grep -v '^import' $LG | grep -v '^#print axioms'
  echo "-- END verbatim body of scratch/local-glue/LocalGlue.lean"
  echo "end"
  echo
  echo "section FrobTraceSec"
  echo "-- BEGIN verbatim body of scratch/frob-trace/FrobTrace.lean (minus l.1632-1754, see build.sh)"
  sed '1632,1754d' $FT | grep -v '^import' | grep -v '^#print axioms'
  echo "-- END verbatim body of scratch/frob-trace/FrobTrace.lean"
  echo "end FrobTraceSec"
  echo
  echo "-- BEGIN verbatim scratch/lg-kerwild/part_kerwild.lean, part_tbk.lean, part_final.lean"
  cat $KW/part_kerwild.lean | grep -v '^#print axioms'
  echo
  cat $KW/part_tbk.lean | grep -v '^#print axioms'
  cat $KW/part_final.lean | grep -v '^#print axioms'
  echo "-- END verbatim lg-kerwild parts"
  echo
  [ -f part_fix.lean ] && cat part_fix.lean
} > KerWildFix.lean
