#!/bin/bash
# SplitIntegrated.lean = g0-split's Split.lean with this task's proofs inserted (integration check)
cd "$(dirname "$0")"
S=../g0-split/Split.lean; P=part_heightadd.lean
{ sed -n 1,18603p $S; sed -n 11,314p $P; sed -n '18604,$p' $S
  echo; echo "namespace HSyn.G0Split"
  echo "open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj"
  echo "open ZInQ ZInQ.DefFaltings"; sed -n 363,384p $P; echo "end HSyn.G0Split"; echo
  sed -n 391,485p $P
  echo "#print axioms HSyn.G0Split.heightAdditivity_of_split"
  echo "/-- The piece of g0-split's own file, closed from the smaller Props. -/"
  echo "example (hN1 : ZInQ.H5Neron.NeronModelExists) (r : HSyn.ResearchLeaves)"
  echo "    (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)"
  echo "    (hD : ZInQ.G0HeightAdd.MetrizationDimUnique) (hE : ZInQ.G0HeightAdd.MetrizationExists)"
  echo "    (hP : ZInQ.G0HeightAdd.ProductMetrization) : HSyn.G0Split.HeightAdditivity :="
  echo "  HSyn.G0Split.heightAdditivity_of_split hN1 r.h5 hU hD hE hP"
} > SplitIntegrated.lean
