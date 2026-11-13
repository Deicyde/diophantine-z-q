#!/bin/bash
# LocalGlue.lean = scratch/local-data/LocalData.lean (verbatim, whole file: it contains `LocalGlue`
# and everything it depends on, itself assembled from verbatim copies of scratch/g15-ram and
# scratch/g0-mod-galois by scratch/local-data/build.sh) + part_glue.lean (new, this task).
cd "$(dirname "$0")"
{
  cat ../local-data/LocalData.lean
  echo
  cat part_glue.lean
} > LocalGlue.lean
