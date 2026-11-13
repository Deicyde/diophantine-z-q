#!/bin/bash
# Assemble PNFull.lean = period-map's light development, verbatim (light_base + part_light + part_theta +
# part_siegel + part_order, i.e. scratch/period-map/PMLight.lean), followed by this task's parts, and check it
# with `lake env lean` (single file, imports Mathlib only). Run from the repository root.
set -e
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=scratch/period-num; M=scratch/period-map
{ cat $M/light_base.lean $M/part_light.lean $M/part_theta.lean $M/part_siegel.lean $M/part_order.lean
  for f in $D/part_nonzero.lean $D/part_weight.lean; do [ -f $f ] && cat $f; done; } > $D/PNFull.lean
lake env lean $D/PNFull.lean
