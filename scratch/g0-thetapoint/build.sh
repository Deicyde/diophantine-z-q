#!/bin/bash
# Assemble ThetaPoint.lean = g0-split's Split.lean (verbatim, plus one import of bp-analytic's
# QMLattice module, which needs `lake build ZInQKernel.HDecomp.Analytic.QMLattice`) + part_theta.lean
cd "$(dirname "$0")"
S=../g0-split/Split.lean
{ sed -n 1,3p $S; echo "import ZInQKernel.HDecomp.Analytic.QMLattice"; sed -n '4,$p' $S; cat part_theta.lean; } > ThetaPoint.lean
