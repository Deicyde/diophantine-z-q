#!/bin/bash
# Assemble FrobTrace.lean = extra import (C10.Link, for FrobCompare)
#   + part_tate_src.lean (verbatim copy of scratch/unram-tate/TateBridge.lean, itself
#     scratch/g0-mod-field/ModField.lean L1-1036 verbatim + section UnramTate)
#   + part_bridge_src.lean (verbatim copy of scratch/g14-trace/part_bridge.lean:
#     G14Bridge.FrobTraceLink, G14Bridge.TateBridge35)
#   + part_frob.lean (this task).
cd "$(dirname "$0")"
{
  echo "import ZInQKernel.HDecomp.C10.Link"
  cat part_tate_src.lean
  cat part_bridge_src.lean
  cat part_frob.lean
} > FrobTrace.lean
