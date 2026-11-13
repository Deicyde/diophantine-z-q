#!/bin/bash
# LocalGlue.lean = scratch/local-data/LocalData.lean (verbatim, whole file: it contains `LocalGlue`
# and everything it depends on, itself assembled from verbatim copies of scratch/g15-ram and
# scratch/g0-mod-galois by scratch/local-data/build.sh)
# + verbatim scratch/g0-mod-galois/part_galois.lean lines 40-58 (`qEmbRing`, `qEmb`, `resQ_spec`)
# + part_glue.lean (§6-§7, new) + part_pack.lean (§8: verbatim `G8LocalPack` from
# scratch/local-data/tail_part.lean, then new).
cd "$(dirname "$0")"
{
  cat ../local-data/LocalData.lean
  echo
  cat galois_block.lean
  cat part_glue.lean
  cat part_pack.lean
} > LocalGlue.lean
