#!/bin/bash
# Assemble NewForm.lean = imports + copy of scratch/c9-rhof/C9.lean (body) + copy of
# scratch/e1-sub/E1Sub.lean (body) + the new section part_new.lean.
cd "$(dirname "$0")"
{
  echo "import ZInQKernel.HDecomp.ModCurves.Glue"
  echo "import ZInQKernel.HDecomp.I3Linalg.C2"
  echo "import ZInQKernel.HDecomp.I3Linalg.RhoCont"
  echo "import ZInQKernel.HDecomp.I3Linalg.TateBC"
  echo "import ZInQKernel.HDecomp.Conductor.Level"
  echo "import ZInQKernel.HDecomp.Assembly"
  echo "import ZInQKernel.Main"
  echo
  echo "/-! Copied from scratch/c9-rhof/C9.lean (compiled there), lines 4-632. -/"
  echo "section C9Copy"
  sed -n 4,632p part_c9_src.lean
  echo "end"
  echo "end C9Copy"
  echo
  echo "/-! Copied from scratch/e1-sub/E1Sub.lean (compiled there), lines 4-870. -/"
  echo "section E1Copy"
  sed -n 4,870p part_e1_src.lean
  echo "end"
  echo "end E1Copy"
  echo
  cat part_new.lean
} > NewForm.lean
