#!/bin/bash
# bc_block.lean: verbatim scratch/unram-tate/BCPoints.lean (origin/wip/unram-tate) l.14-142
# (`UnramTate.bcPt`, `bcPt_galAct`, `trPt`, `trPt_galAct`).
cd "$(dirname "$0")"
git show origin/wip/unram-tate:scratch/unram-tate/BCPoints.lean > /tmp/bcpoints_src.lean
{ echo
  echo "/-! ## §7c'' (local-glue). Verbatim copy of scratch/unram-tate/BCPoints.lean"
  echo "(origin/wip/unram-tate) l.14-142 -/"
  echo; echo "noncomputable section"; echo
  sed -n 14,142p /tmp/bcpoints_src.lean
  echo; echo "end"; echo; } > bc_block.lean
