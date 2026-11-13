#!/bin/bash
# Assemble FibreQM.lean (run from the repository root):
#   g0-thetapoint's ThetaPoint.lean with qm-pin's full edit of R1fpProps (scratch/qm-pin/apply_edit.py)
#   + part_pin.lean (qm-pin's comparison lemmas, verbatim) + part_fqm.lean (this task).
# Prerequisites: lake build ZInQKernel.HDecomp.Analytic.QMLattice ZInQKernel.Hypotheses.JHeight
set -e
D=scratch/fibre-qm-period
python3 scratch/qm-pin/apply_edit.py scratch/g0-thetapoint/ThetaPoint.lean $D/FQMBase.lean full
cat $D/part_pin.lean >> $D/FQMBase.lean
{ cat $D/FQMBase.lean; cat $D/part_fqm.lean; } > $D/FibreQM.lean
