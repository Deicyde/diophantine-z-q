#!/bin/bash
# Assemble ZariskiConnFull.lean =
#   the 21 import lines of src_FrobPiecesFull.lean (a cmp-identical copy of frob-pieces' assembled
#     scratch/frob-pieces/FrobPiecesFull.lean)
#   + import ZInQKernel.Contrib.ZariskiConn.Basic (this task's Contrib file)
#   + the rest of src_FrobPiecesFull.lean
#   + part_zc.lean (this task).
# Check: lake env lean scratch/zariski-conn/ZariskiConnFull.lean
cd "$(dirname "$0")"
cmp src_FrobPiecesFull.lean ../frob-pieces/FrobPiecesFull.lean || echo "WARNING: src_FrobPiecesFull.lean differs from scratch/frob-pieces/FrobPiecesFull.lean"
{
  head -21 src_FrobPiecesFull.lean
  echo "import ZInQKernel.Contrib.ZariskiConn.Basic"
  tail -n +22 src_FrobPiecesFull.lean
  cat part_zc.lean
} > ZariskiConnFull.lean
