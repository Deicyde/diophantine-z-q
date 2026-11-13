#!/bin/bash
# Assemble G14Trace.lean = imports + verbatim copies of scratch/g0-mod-newform/{part_c9_src,
# part_e1_src,part_new}.lean (exactly as scratch/g0-mod-newform/build.sh assembles NewForm.lean)
# + the new section part_g14.lean. Extra import: ZInQKernel.HDecomp.C10.Link (FrobCompare).
cd "$(dirname "$0")"
{
  echo "import ZInQKernel.HDecomp.ModCurves.Glue"
  echo "import ZInQKernel.HDecomp.I3Linalg.C2"
  echo "import ZInQKernel.HDecomp.I3Linalg.RhoCont"
  echo "import ZInQKernel.HDecomp.I3Linalg.TateBC"
  echo "import ZInQKernel.HDecomp.Conductor.Level"
  echo "import ZInQKernel.HDecomp.Assembly"
  echo "import ZInQKernel.HDecomp.C10.Link"
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
  echo "/-! Copied verbatim from scratch/g0-mod-newform/part_new.lean. -/"
  cat part_new.lean
  echo
  cat part_g14.lean
} > G14Trace.lean
