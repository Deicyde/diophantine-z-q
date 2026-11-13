#!/bin/bash
# TailK.lean = scratch/local-data/Tail.lean (verbatim, whole file: g0-mod-newform's tail with
# local-data's `modularConstituent_tail_L`) + galois_block.lean + part_glue.lean (§6-§7) + part_pack.lean without its
# verbatim copy of `G8LocalPack` (already in Tail.lean) + tail_glue.lean (§9).
cd "$(dirname "$0")"
{
  cat ../local-data/Tail.lean
  echo
  cat galois_block.lean
  grep -v '^#print axioms' part_glue.lean
  sed '/^-- BEGIN verbatim copy/,/^-- END verbatim copy/d' part_pack.lean | grep -v '^#print axioms'
  cat tail_glue.lean
} > TailK.lean
