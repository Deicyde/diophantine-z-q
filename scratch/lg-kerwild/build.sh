#!/bin/bash
# KerWild.lean = imports (union) + scratch/local-glue/LocalGlue.lean body (verbatim; it contains
# `KerWild`, `DescentPts`, `localGlue_of_unramRoots`, `descentPts_baseChange` and everything they
# depend on) + `end` (closes its unclosed top-level `noncomputable section`)
# + scratch/g14-trace/G14Bridge.lean body (verbatim: g0-mod-field's ModField.lean with `G7Data`,
# `TateBridge`, and g14-trace's `TateBridge35`), in a section
# + scratch/g0-dim/Dim.lean l.107-305 and l.339-344 (verbatim: `G0Dim.dim_baseChange`,
# `G0Dim.pkgI3_dim_baseChange`), in a section
# + part_kerwild.lean (new).
# `#print axioms` lines of the copies are dropped; import lines are collected at the top.
cd "$(dirname "$0")"
LG=../local-glue/LocalGlue.lean
GB=../g14-trace/G14Bridge.lean
DM=../g0-dim/Dim.lean
{
  cat $LG $GB | grep '^import' | awk '!seen[$0]++'
  echo
  echo "-- BEGIN verbatim body of scratch/local-glue/LocalGlue.lean"
  grep -v '^import' $LG | grep -v '^#print axioms'
  echo "-- END verbatim body of scratch/local-glue/LocalGlue.lean"
  echo "end"
  echo
  echo "section G14BridgeSec"
  echo "-- BEGIN verbatim body of scratch/g14-trace/G14Bridge.lean"
  grep -v '^import' $GB | grep -v '^#print axioms'
  echo "-- END verbatim body of scratch/g14-trace/G14Bridge.lean"
  echo "end G14BridgeSec"
  echo
  echo "section G0DimSec"
  echo "set_option linter.style.haveILetI false"
  echo "set_option linter.unusedSectionVars false"
  echo "open Order TensorProduct"
  echo "-- BEGIN verbatim scratch/g0-dim/Dim.lean l.107-305, l.339-344"
  sed -n 107,305p $DM
  sed -n 339,344p $DM
  echo "-- END verbatim scratch/g0-dim/Dim.lean"
  echo "end G0DimSec"
  echo
  cat part_kerwild.lean
} > KerWild.lean
