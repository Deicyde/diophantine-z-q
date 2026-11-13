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
# + scratch/unram-roots/UnramRoots.lean l.53-end (verbatim; proves `G15Ram.UnramRoots`).
# + part_fix.lean (new, kerwild-fix; made by mk_fix.py from part_fix_head/defs/final.lean and
#   two edited copies of frob-trace's tateBridge35_of_algFrobLink).
# `#print axioms` lines of the copies are dropped.
cd "$(dirname "$0")"
LG=../local-glue/LocalGlue.lean
FT=../frob-trace/FrobTrace.lean
KW=../lg-kerwild
UR=../unram-roots
{
  cat $LG $FT | grep '^import' | awk '!seen[$0]++'
  # for g8-tate's `exists_complex_equiv` (part_fix.lean §0)
  echo "import Mathlib.Analysis.Complex.Cardinality"
  echo "import Mathlib.Topology.Algebra.Module.Cardinality"
  echo "import Mathlib.FieldTheory.IsAlgClosed.Classification"
  # for unram-roots (UnramRoots.lean's Tau Ceti imports)
  grep '^import ZInQKernel.Contrib' $UR/UnramRoots.lean
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
  echo "section UnramRootsSec"
  echo "-- BEGIN verbatim scratch/unram-roots/UnramRoots.lean l.53-end (l.1-52: imports, module doc,"
  echo "-- and its copy of local-glue's \`G15Ram.UnramRoots\`, already in LocalGlue.lean, byte-identical"
  echo "-- per rv-fast §3); two \`end\` close its unclosed \`noncomputable section\`s (l.204, l.475)"
  sed -n '53,$p' $UR/UnramRoots.lean | grep -v '^#print axioms'
  echo "end"
  echo "end"
  echo "-- END verbatim unram-roots"
  echo "end UnramRootsSec"
  echo
  [ -f part_fix.lean ] && cat part_fix.lean
} > KerWildFix.lean
