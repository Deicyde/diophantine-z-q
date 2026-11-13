#!/bin/bash
# Integration check: SplitMetrization.lean = g0-heightadd's SplitIntegrated.lean (g0-split's
# Split.lean with g0-heightadd's proofs) + this task's parts + a final `example` closing
# `HSyn.G0Split.HeightAdditivity` with `r.h5` from `HSyn.ResearchLeaves`. Generated, not committed.
cd "$(dirname "$0")"
{ cat ../g0-heightadd/SplitIntegrated.lean
  sed -e '/^import Mathlib/d' -e '/^#print axioms/d' ExtLine.lean
  for f in part_dim.lean part_g0dim.lean part_exists.lean part_prodgeo.lean part_prodlat.lean \
      part_final.lean part_produnif.lean part_jacdet.lean part_prodsplit.lean part_jacgerm.lean \
      part_jacscalar.lean part_jacclass.lean part_prodjac.lean part_produnif2.lean; do cat $f; done
  echo
  echo "/-- The piece of g0-split's own file, from this task's smaller Props. -/"
  echo "example (hN1 : ZInQ.H5Neron.NeronModelExists) (r : HSyn.ResearchLeaves)"
  echo "    (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)"
  echo "    (hH : ZInQ.DefFaltings.HodgeLatticeTheorem)"
  echo "    (hUD : ZInQ.Metrization.AnalyticUniformizationOfDim)"
  echo "    (hN : ZInQ.Metrization.JacDetNondegenerate)"
  echo "    (hLS : ZInQ.Metrization.ProductLocalStructure)"
  echo "    (hPL : ZInQ.Metrization.ProductHodgeLattice) : HSyn.G0Split.HeightAdditivity :="
  echo "  HSyn.G0Split.heightAdditivity_of_metrization_v3 hN1 r.h5 hU hH hUD hN hLS hPL"
  echo "#print axioms HSyn.glueOutputs_of_leaves"
  echo "#print axioms HSyn.sixContactMin_of_leaves"
} > SplitMetrization.lean
