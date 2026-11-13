#!/bin/bash
# LocalGlue.lean = scratch/local-data/LocalData.lean (verbatim, whole file: it contains `LocalGlue`
# and everything it depends on, itself assembled from verbatim copies of scratch/g15-ram and
# scratch/g0-mod-galois by scratch/local-data/build.sh)
# + verbatim scratch/g0-mod-galois/part_galois.lean lines 40-58 (`qEmbRing`, `qEmb`, `resQ_spec`)
# + part_glue.lean (§6-§7, new) + part_ptfinite.lean (§7b, new; needs the extra Mathlib import
# AffineTransitionLimit, put first) + neron_block.lean (verbatim slices of scratch/neron-lg, made by
# mk_neron_block.sh) + bc_block.lean (verbatim scratch/unram-tate/BCPoints.lean l.14-142, made by
# mk_bc_block.sh) + part_raynaud.lean (§7c, new) + part_pack.lean (§8: verbatim `G8LocalPack` from
# scratch/local-data/tail_part.lean, then new).
cd "$(dirname "$0")"
{
  echo "import Mathlib.AlgebraicGeometry.AffineTransitionLimit"
  echo "import Mathlib.NumberTheory.NumberField.Completion.FinitePlace"
  cat ../local-data/LocalData.lean
  echo
  cat galois_block.lean
  cat part_glue.lean
  cat part_ptfinite.lean
  cat neron_block.lean
  cat bc_block.lean
  cat part_raynaud.lean
  cat part_pack.lean
} > LocalGlue.lean
