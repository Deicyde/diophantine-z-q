#!/bin/bash
# Assemble G14Bridge.lean = verbatim copy (part_modfield_src.lean) of scratch/g0-mod-field/ModField.lean (with the extra
# import ZInQKernel.HDecomp.C10.Link) + part_bridge.lean.
cd "$(dirname "$0")"
{
  echo "import ZInQKernel.HDecomp.C10.Link"
  cat part_modfield_src.lean
  cat part_bridge.lean
} > G14Bridge.lean
