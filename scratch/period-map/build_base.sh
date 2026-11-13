#!/bin/bash
# PMBase.lean = fibre-qm-period's assembled FibreQM.lean (copied verbatim), compiled to an olean.
# Run from the repository root. Prerequisites:
#   lake build ZInQKernel.HDecomp.Analytic.QMLattice ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant
set -e
D=scratch/period-map
cp scratch/fibre-qm-period/FibreQM.lean $D/PMBase.lean
lake env lean -o $D/olean/PMBase.olean $D/PMBase.lean
