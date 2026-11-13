#!/bin/bash
# Assemble SpreadOutFull.lean =
#   the 21 import lines of scratch/frob-pieces/FrobPiecesFull.lean (frob-pieces' assembled file,
#     used unchanged; it contains frob-pieces' verbatim copy of N1-g1 `FrobPiecesNeron.AbVarSpreadsOut`)
#   + import ZInQKernel.Contrib.SpreadOut.NumberField (this task's Contrib file)
#   + the rest of FrobPiecesFull.lean
#   + part_full.lean (this task).
# Check (from the repository root): lake env lean scratch/spread-out/SpreadOutFull.lean
cd "$(dirname "$0")"
SRC=../frob-pieces/FrobPiecesFull.lean
{
  head -21 $SRC
  echo "import ZInQKernel.Contrib.SpreadOut.NumberField"
  tail -n +22 $SRC
  cat part_full.lean
} > SpreadOutFull.lean
