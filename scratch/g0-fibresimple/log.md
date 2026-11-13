# g0-fibresimple results log

## Setup
- 01:45 merged origin/wip/g0-split (base for Split.lean). FibreSimple's statement is identical in
  origin/wip/leaf-adopt3's Leaves.lean (VERIFIED by grep).
- Infrastructure: `olean/FSPrefix.lean` = verbatim copy of scratch/g0-split/Split.lean (gitignored; regenerate
  with build_prefix.sh), compiled to an olean; `olean/Tail.lean` imports it (`ctail.sh`).
- `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant` was needed first (OK).
