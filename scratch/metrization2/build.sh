#!/bin/bash
# Assemble Metrization2.lean (self-contained, `import Mathlib` only):
#   base/Base.lean (verbatim copy of scratch/metrization/Base.lean = scratch/g0-heightadd/HeightAdd.lean)
#   + base/ExtLine.lean body + base/part_*.lean in metrization's build.sh order
#   + this task's parts.
cd "$(dirname "$0")"
{ cat base/Base.lean
  sed -e '/^import Mathlib/d' -e '/^#print axioms/d' base/ExtLine.lean
  for f in part_dim part_g0dim part_exists part_prodgeo part_prodlat part_final part_produnif \
      part_jacdet part_prodsplit part_jacgerm part_jacscalar part_jacclass part_prodjac part_produnif2; do
    sed -e '/^#print axioms/d' base/$f.lean
  done
  for f in part_nondeg1 part_nondeg2 part_nondeg3 part_unif0 part_unif1; do
    sed -e '/^#print axioms/d' $f.lean
  done
  cat part_final2.lean
} > Metrization2.lean
