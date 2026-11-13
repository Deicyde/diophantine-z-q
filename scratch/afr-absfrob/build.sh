#!/bin/bash
# Assemble AfrAbsFrob.lean =
#   src_AlgFrobRed.lean (verbatim copy of scratch/alg-frob-red/AlgFrobRed.lean, which already
#     defines AlgFrobRedRed.AbsFrob and AlgFrobRedRed.FExtendGen)
#   + AbsFrobDef.lean without its import line and without its copy of `def AbsFrob`
#     (the absolute Frobenius, Mathlib only)
#   + part_fext.lean (FExtendGen from I2-NMP, and the final assembly).
cd "$(dirname "$0")"
{
  cat src_AlgFrobRed.lean
  tail -n +2 AbsFrobDef.lean | sed '/^\/-- \*\*`AbsFrob` (GLUE/,/≫ g = g ≫ Fr$/d'
  cat part_fext.lean
} > AfrAbsFrob.lean
