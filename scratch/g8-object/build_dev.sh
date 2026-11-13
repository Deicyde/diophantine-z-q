#!/bin/bash
# Assemble Dev.lean = scratch/g15-ram/G15Ram.lean (verbatim, two extra imports appended after its
# own) + verbatim copies of g0-mod-galois' definitions (part_galois.lean L27-152: resQ ... G8Out;
# part_matrix.lean L11-21: BurnsideAbsIrred) + part_obj.lean.
cd "$(dirname "$0")"
{
  sed -n '1,7p' ../g15-ram/G15Ram.lean
  echo "import ZInQKernel.HDecomp.Descent.ProjRep"
  echo "import ZInQKernel.HDecomp.I3Linalg.C2"
  sed -n '8,$p' ../g15-ram/G15Ram.lean
  echo
  echo "/-! Copied verbatim from scratch/g0-mod-galois/part_galois.lean L27-152 and part_matrix.lean L11-21. -/"
  echo "noncomputable section"
  sed -n '27,152p' ../g0-mod-galois/part_galois.lean
  echo
  sed -n '11,21p' ../g0-mod-galois/part_matrix.lean
  echo
  echo "end G0Galois"
  echo "end"
  cat part_obj.lean
} > Dev.lean
