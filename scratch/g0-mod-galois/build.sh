#!/bin/bash
# Iter.lean = Leaves.lean prefix (through DescProjRepSec, line 7776) + part_galois.lean  (fast iteration)
# ModGalois.lean = g0-split's Split.lean + part_galois.lean + part_matrix.lean + part_det.lean + part_bundle.lean
cd "$(dirname "$0")"
S=../g0-split/Split.lean
# (Iter.lean dropped: the part uses T09, T11, T12 from later sections)
{ cat $S; cat part_galois.lean; cat part_matrix.lean; cat part_det.lean; cat part_bundle.lean; } > ModGalois.lean
