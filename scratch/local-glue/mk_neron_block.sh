#!/bin/bash
# neron_block.lean: verbatim slices of scratch/neron-lg/NeronLG.lean on origin/wip/neron-lg
# (l.207-215 `dvrAt` + instance; l.225-236 `ringOfIntegers_mem`, `toO`, `toO_coe`;
#  l.1406-1472 §9 `center'`, `dvrAt_center'`, `isDiscreteValuationRing_of_ne_top`).
cd "$(dirname "$0")"
git show origin/wip/neron-lg:scratch/neron-lg/NeronLG.lean > /tmp/neronlg_src.lean
S=/tmp/neronlg_src.lean
{ echo
  echo "/-! ## §7c' (local-glue). Verbatim slices of scratch/neron-lg/NeronLG.lean (origin/wip/neron-lg)"
  echo "l.207-215, l.225-236, l.1406-1472 -/"
  echo; echo "noncomputable section"; echo; echo "namespace ZInQ.NeronLG"; echo
  echo "open NumberField"; echo "open CategoryTheory MonObj"; echo
  sed -n 207,215p $S
  echo; echo "section Classify"; echo; echo "set_option linter.unusedSectionVars false"; echo
  echo "variable {K : Type} [Field K] [NumberField K]"; echo
  sed -n 225,236p $S
  echo; echo "end Classify"; echo
  sed -n 1406,1472p $S
  echo; echo "end ZInQ.NeronLG"; echo; echo "end"; echo; } > neron_block.lean
