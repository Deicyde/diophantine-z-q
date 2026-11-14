#!/bin/bash
# PGLight.lean = period-map's PMLight.lean (light_base.lean = pkg-I1's PkgI1 block and part_fqm's light
# statements, verbatim, + part_light, part_theta, part_siegel, part_order), copied verbatim; imports
# Mathlib only. Compiled to olean/PGLight.olean. Run from the repository root.
set -e
D=scratch/period-glue; M=scratch/period-map
cp $M/PMLight.lean $D/PGLight.lean
mkdir -p $D/olean
lake env lean -o $D/olean/PGLight.olean $D/PGLight.lean
