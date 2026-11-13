#!/bin/bash
# Assemble and check DevHeavy.lean = import PMBase + the light parts + part_heavy.lean (run from the repository root,
# after build_base.sh has produced olean/PMBase.olean).
set -e
D=scratch/period-map
{ echo "import PMBase"; cat $D/part_light.lean $D/part_theta.lean $D/part_siegel.lean $D/part_order.lean $D/part_heavy.lean; } > $D/DevHeavy.lean
LEAN_PATH=$(lake env printenv LEAN_PATH):$D/olean lean $D/DevHeavy.lean
