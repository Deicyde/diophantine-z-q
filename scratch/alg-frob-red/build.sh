#!/bin/bash
# Assemble AlgFrobRed.lean =
#   imports: ZInQKernel.HDecomp.C10.Link (frob-trace's) + the Mathlib imports of src_Rigidity.lean
#   + frob-trace's FrobTrace.lean body: src_part_tate_src.lean, src_part_bridge_src.lean, src_part_frob.lean
#     (verbatim copies of origin/wip/frob-trace:scratch/frob-trace/{part_tate_src,part_bridge_src,part_frob}.lean)
#   + src_Rigidity.lean without its 4 import lines (verbatim copy of scratch/mul-rigidity/Rigidity.lean:
#     G0FibreSimple.rigidityHom, proved from Mathlib)
#   + part_red.lean (this task).
cd "$(dirname "$0")"
{
  echo "import ZInQKernel.HDecomp.C10.Link"
  head -4 src_Rigidity.lean | grep -v "ZInQKernel.HDecomp.Objects"
  cat src_part_tate_src.lean
  cat src_part_bridge_src.lean
  cat src_part_frob.lean
  tail -n +5 src_Rigidity.lean
  cat part_red.lean
} > AlgFrobRed.lean
