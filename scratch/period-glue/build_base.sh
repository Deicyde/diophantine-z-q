#!/bin/bash
# PGBase.lean = period-map's PMBase.lean (fibre-qm-period's FibreQM.lean lines 1-20634 + part_fqm.lean)
# + period-map's part_light, part_theta, part_siegel, part_order, part_heavy (= DevHeavy.lean without
# its `import PMBase`), all verbatim. Compiled to olean/PGBase.olean. Run from the repository root
# after: lake build ZInQKernel.HDecomp.Analytic.QMLattice ZInQKernel.Hypotheses.JHeight \
#   ZInQKernel.Compiler.Precision.HeightConstant
set -e
D=scratch/period-glue; F=scratch/fibre-qm-period; M=scratch/period-map
head -n 20634 $F/FibreQM.lean > $D/PGBase.lean
cat $F/part_fqm.lean $M/part_light.lean $M/part_theta.lean $M/part_siegel.lean $M/part_order.lean \
  $M/part_heavy.lean >> $D/PGBase.lean
mkdir -p $D/olean
lake env lean -o $D/olean/PGBase.olean $D/PGBase.lean
