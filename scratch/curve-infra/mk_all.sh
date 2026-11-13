#!/bin/sh
# Assemble CurveInfraAll.lean: imports; infra-smooth-dim's SmoothStalk.lean (verbatim, lines 2-526);
# Dim.lean (without its import and #print lines); tail_part.lean.part.
cd "$(dirname "$0")"
{
  echo "import Mathlib"
  echo "import ZInQKernel.HDecomp.LeafPush2.R18"
  sed -n '2,526p' ../infra-smooth-dim/SmoothStalk.lean
  echo
  grep -v '^import\|^#print' Dim.lean
  cat tail_part.lean.part
} > CurveInfraAll.lean
