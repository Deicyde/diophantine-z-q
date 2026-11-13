#!/bin/bash
# Assemble PGLight.lean = period-map light_base + part_light/theta/siegel/order (verbatim; = its PMLight.lean; imports Mathlib only)
# + gen_sphere.lean + part_sphere.lean, and check it with lake env lean. Run from the repository root.
set -e
D=scratch/period-glue; M=scratch/period-map
cat $M/light_base.lean $M/part_light.lean $M/part_theta.lean $M/part_siegel.lean $M/part_order.lean $D/gen_sphere.lean $D/part_sphere.lean > $D/PGLight.lean
lake env lean $D/PGLight.lean
