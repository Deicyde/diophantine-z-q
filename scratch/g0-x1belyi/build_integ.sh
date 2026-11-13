#!/bin/bash
# Integration check: Integ.lean = scratch/g0-split/Split.lean (as committed by g0-split, c20fa62b)
# + body of scratch/x1-belyi/X1Belyi.lean (lines 2-365) + the G0X1Belyi part of part_onmodel.lean
# (without the copied HSyn.G0Split block, which Split.lean already defines) + part_final.lean
# + part_integ.lean. Check: lake env lean scratch/g0-x1belyi/Integ.lean
cd "$(dirname "$0")"
{ cat ../g0-split/Split.lean; echo
  sed -n 2,365p ../x1-belyi/X1Belyi.lean
  sed '/^namespace HSyn.G0Split/,/^end HSyn.G0Split/d' part_onmodel.lean
  cat part_final.lean part_integ.lean; } > Integ.lean
