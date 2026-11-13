#!/bin/bash
# Assemble PMFull.lean = PMBase.lean (see build_base.sh) + all period-map parts, and check it with lake env lean.
# Run from the repository root after the prerequisites of build_base.sh. PMFull.lean is not committed (22k lines).
set -e
D=scratch/period-map; F=scratch/fibre-qm-period
{ head -n 20634 $F/FibreQM.lean; cat $F/part_fqm.lean $D/part_light.lean $D/part_theta.lean $D/part_siegel.lean $D/part_order.lean $D/part_heavy.lean; } > $D/PMFull.lean
lake env lean $D/PMFull.lean
