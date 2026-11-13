#!/bin/bash
# Assemble FrobTraceAll.lean: one environment with FrobTrace.lean's parts and verbatim copies
# of g14-trace's G14Trace.lean parts (part_c9_src_g14, part_e1_src_g14, part_new_g14,
# part_g14_g14 = scratch/g14-trace/{part_c9_src,part_e1_src,part_new,part_g14}.lean, assembled
# exactly as scratch/g14-trace/build.sh does), plus part_compose.lean.
cd "$(dirname "$0")"
{
  # g14-trace's imports first, in its order, then those of part_tate_src.lean
  echo "import ZInQKernel.HDecomp.ModCurves.Glue"
  echo "import ZInQKernel.HDecomp.I3Linalg.C2"
  echo "import ZInQKernel.HDecomp.I3Linalg.RhoCont"
  echo "import ZInQKernel.HDecomp.I3Linalg.TateBC"
  echo "import ZInQKernel.HDecomp.Conductor.Level"
  echo "import ZInQKernel.HDecomp.Assembly"
  echo "import ZInQKernel.HDecomp.C10.Link"
  echo "import ZInQKernel.Main"
  grep '^import' part_tate_src.lean
  echo
  echo "/-! Copied from scratch/c9-rhof/C9.lean (compiled there), lines 4-632. -/"
  echo "section C9Copy"
  sed -n 4,632p part_c9_src_g14.lean
  echo "end"
  echo "end C9Copy"
  echo
  echo "/-! Copied from scratch/e1-sub/E1Sub.lean (compiled there), lines 4-870. -/"
  echo "section E1Copy"
  sed -n 4,870p part_e1_src_g14.lean
  echo "end"
  echo "end E1Copy"
  echo
  echo "/-! Copied verbatim from scratch/g0-mod-newform/part_new.lean. -/"
  cat part_new_g14.lean
  echo
  cat part_g14_g14.lean
  echo
  grep -v '^import' part_tate_src.lean
  cat part_bridge_src.lean
  cat part_frob.lean
  cat part_compose.lean
} > FrobTraceAll.lean
