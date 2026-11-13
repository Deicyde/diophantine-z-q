#!/bin/bash
# PMBase.lean = fibre-qm-period's FQMBase part of FibreQM.lean (lines 1-20634: g0-thetapoint's ThetaPoint.lean with
# qm-pin's full edit, then part_pin.lean) + the current scratch/fibre-qm-period/part_fqm.lean, all verbatim.
# (The committed FibreQM.lean predates part_fqm's last step: it lacks qmSkolemNoetherC_proof and fibreQMPeriod_main.)
# Run from the repository root. Prerequisites:
#   lake build ZInQKernel.HDecomp.Analytic.QMLattice ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant
set -e
D=scratch/period-map; F=scratch/fibre-qm-period
head -n 20634 $F/FibreQM.lean > $D/PMBase.lean
cat $F/part_fqm.lean >> $D/PMBase.lean
lake env lean -o $D/olean/PMBase.olean $D/PMBase.lean
