#!/bin/bash
# Prefix.lean: one environment holding g8-object's checked file and local-glue's checked file.
#  imports (union) +
#  scratch/g8-object/G8Object.lean lines 28-end (verbatim; itself assembled by g8-object/build.sh) +
#  scratch/local-data/part_local.lean (verbatim; local-data's §4, the part of LocalData.lean after
#    its copies of G15Ram.lean and part_galois.lean, which G8Object.lean already contains), inside
#    a `noncomputable section` (in LocalData.lean, G15Ram.lean's file-level one is open there) +
#  local-glue's parts (verbatim), in local-glue/build.sh's order, without galois_block.lean
#    (= part_galois.lean L40-58, already in G8Object.lean's copy of L27-152).
cd "$(dirname "$0")"
G=../g8-object/G8Object.lean
LG=../local-glue
{
  sed -n '1,27p' $G
  echo "import Mathlib.AlgebraicGeometry.AffineTransitionLimit"
  echo "import Mathlib.NumberTheory.NumberField.Completion.FinitePlace"
  echo "import ZInQKernel.HDecomp.Descent.B2Glue"
  echo "import ZInQKernel.HDecomp.Descent.Chi"
  echo "import ZInQKernel.Contrib.AbVarBC.Dim"
  sed -n '28,$p' $G
  echo
  echo "/-! Copied verbatim from scratch/local-data/part_local.lean. -/"
  echo "noncomputable section"
  cat ../local-data/part_local.lean
  echo "end"
  echo
  echo "/-! Copied verbatim from scratch/local-glue/ (part_glue, part_ptfinite, neron_block, bc_block,"
  echo "part_raynaud, resq_block, part_descent, part_twist, part_bcdescent, part_pack). -/"
  for f in part_glue part_ptfinite neron_block bc_block part_raynaud resq_block part_descent part_twist part_bcdescent part_pack; do
    cat $LG/$f.lean
    echo
  done
} > Prefix.lean
