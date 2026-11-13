#!/bin/bash
# Assemble AlgFrobRed.lean = frob-trace's FrobTrace.lean (its build.sh: import C10.Link + the three
# parts, copied verbatim here as src_*.lean from origin/wip/frob-trace:scratch/frob-trace/) + part_red.lean.
cd "$(dirname "$0")"
{
  echo "import ZInQKernel.HDecomp.C10.Link"
  cat src_part_tate_src.lean
  cat src_part_bridge_src.lean
  cat src_part_frob.lean
  cat part_red.lean
} > AlgFrobRed.lean
