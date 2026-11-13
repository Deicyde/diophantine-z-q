#!/bin/bash
# Assemble FrobPiecesFull.lean =
#   the 20 import lines of src_AfrAbsFrob.lean (a cmp-identical copy of afr-absfrob's assembled
#     scratch/afr-absfrob/AfrAbsFrob.lean, which is alg-frob-red's AlgFrobRed.lean + afr-absfrob's
#     AbsFrob and FExtendGen parts)
#   + import ZInQKernel.Contrib.FrobPieces.SmoothGeomConnIntegral (this task's Contrib file)
#   + the rest of src_AfrAbsFrob.lean
#   + part_good.lean + part_neron.lean + part_final.lean + part_full.lean (this task).
# Check: lake env lean scratch/frob-pieces/FrobPiecesFull.lean
cd "$(dirname "$0")"
cmp src_AfrAbsFrob.lean ../afr-absfrob/AfrAbsFrob.lean || echo "WARNING: src_AfrAbsFrob.lean differs from scratch/afr-absfrob/AfrAbsFrob.lean"
{
  head -20 src_AfrAbsFrob.lean
  echo "import ZInQKernel.Contrib.FrobPieces.SmoothGeomConnIntegral"
  tail -n +21 src_AfrAbsFrob.lean
  cat part_good.lean
  cat part_neron.lean
  cat part_final.lean
  cat part_full.lean
} > FrobPiecesFull.lean
