#!/bin/bash
# KerWild.lean =
#   imports (union of the sources' imports)
# + scratch/local-glue/LocalGlue.lean body (verbatim; contains `KerWild`, `DescentPts`,
#   `localGlue_of_unramRoots`, `descentPts_baseChange`, local-data's `LocalData`, `G7Clauses`,
#   `LocalGlue` and everything they depend on) + `end` (closes its unclosed top-level
#   `noncomputable section`)
# + scratch/frob-trace/FrobTrace.lean body (verbatim: g0-mod-field's ModField.lean with `G7Data`,
#   `TateBridge`; unram-tate's TateBridge.lean (`tateBridge_of_pieces`, `scalarTransfer`,
#   `tatePoints`, ...); g14-trace's `TateBridge35`; frob-trace's `tateBridge35_of_algFrobRed`),
#   in a section, WITHOUT its lines 1632-1754: these are unram-tate's BCPoints block (`sK` ...
#   `trPt_galAct`, namespace `UnramTate`), already present verbatim in LocalGlue.lean
#   (local-glue's bc_block.lean l.11-134; `diff` identical modulo blank lines)
# + scratch/g0-dim/Dim.lean l.107-305 and l.339-344 (verbatim: `G0Dim.dim_baseChange`,
#   `G0Dim.pkgI3_dim_baseChange`), in a section
# + part_kerwild.lean (new, §1-§4) + part_tbk.lean (new, §5; made by mk_tbk.py)
# + part_final.lean (new, §6).
# `#print axioms` lines of the copies are dropped.
cd "$(dirname "$0")"
LG=../local-glue/LocalGlue.lean
FT=../frob-trace/FrobTrace.lean
DM=../g0-dim/Dim.lean
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
  echo
  cat part_tbk.lean
  cat part_final.lean
} > KerWild.lean
