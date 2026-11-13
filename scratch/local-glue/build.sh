#!/bin/bash
# LocalGlue.lean = scratch/local-data/LocalData.lean (verbatim, whole file: it contains `LocalGlue`
# and everything it depends on, itself assembled from verbatim copies of scratch/g15-ram and
# scratch/g0-mod-galois by scratch/local-data/build.sh)
# + verbatim scratch/g0-mod-galois/part_galois.lean lines 40-58 (`qEmbRing`, `qEmb`, `resQ_spec`)
# + part_glue.lean (§6-§7, new) + part_ptfinite.lean (§7b, new; needs the extra Mathlib import
# AffineTransitionLimit, put first) + neron_block.lean (verbatim slices of scratch/neron-lg, made by
# mk_neron_block.sh) + bc_block.lean (verbatim scratch/unram-tate/BCPoints.lean l.14-142, made by
# mk_bc_block.sh) + part_raynaud.lean (§7c, new) + resq_block.lean (verbatim
# scratch/g0-assemble/parts/75_modfield.lean l.786, l.895-985, renamed; mk_resq_block.sh)
# + part_descent.lean (§7d, new) + part_twist.lean (§7e, new) + dim_block.lean (verbatim
# scratch/g0-dim/Dim.lean l.23, l.107-305, l.339-343; mk_dim_block.sh; its Mathlib imports, found
# by a test compile, are in dim_imports.txt and are put first)
# + part_bcdescent.lean (§7f, new)
# + part_pack.lean (§8: verbatim `G8LocalPack` from
# scratch/local-data/tail_part.lean, then new).
cd "$(dirname "$0")"
{
  cat dim_imports.txt
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
  cat resq_block.lean
  cat part_descent.lean
  cat part_twist.lean
  cat dim_block.lean
  cat part_bcdescent.lean
  cat part_pack.lean
} > LocalGlue.lean
