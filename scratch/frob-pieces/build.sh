#!/bin/bash
# Assemble FrobPieces.lean =
#   the 20 import lines of src_AlgFrobRed.lean (a cmp-identical copy of scratch/alg-frob-red/AlgFrobRed.lean)
#   + import ZInQKernel.Contrib.FrobPieces.SmoothGeomConnIntegral (this task's Contrib file)
#   + the rest of src_AlgFrobRed.lean
#   + part_good.lean + part_final.lean (this task).
# Check: lake env lean scratch/frob-pieces/FrobPieces.lean
cd "$(dirname "$0")"
cmp src_AlgFrobRed.lean ../alg-frob-red/AlgFrobRed.lean || echo "WARNING: src_AlgFrobRed.lean differs from scratch/alg-frob-red/AlgFrobRed.lean"
{
  head -20 src_AlgFrobRed.lean
  echo "import ZInQKernel.Contrib.FrobPieces.SmoothGeomConnIntegral"
  tail -n +21 src_AlgFrobRed.lean
  cat part_good.lean
  cat part_final.lean
} > FrobPieces.lean
