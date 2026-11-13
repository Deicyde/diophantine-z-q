#!/bin/bash
# Assemble All.lean = kernel imports + copy of scratch/t-different/Herbrand.lean (TDifferent part,
# lines 60-1248, and the proof of PkgI6.herbrandQuotient; the PkgI6 definitions come from the
# kernel's I6Base, character-for-character the same) + Swan.lean + Bridge.lean + the final theorem.
cd "$(dirname "$0")"
{
  echo "import ZInQKernel.HDecomp.Conductor.LadicCond"
  echo "import ZInQKernel.HDecomp.Conductor.I6Base"
  echo
  echo "/-! Copied from scratch/t-different/Herbrand.lean (compiled there), lines 60-1248. -/"
  echo "section TDiffCopy"
  echo "open IsLocalRing Polynomial MeasureTheory Set"
  sed -n 60,1248p tdiff_herbrand_src.lean
  echo "end TDiffCopy"
  echo
  echo "namespace PkgI6"
  echo "open IsLocalRing"
  echo "attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra"
  echo "/-- **T22a (\`PkgI6.HerbrandQuotient\`): proved** (copied from scratch/t-different/Herbrand.lean). -/"
  echo "theorem herbrandQuotient : HerbrandQuotient := by"
  echo "  intro A C B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r hr v"
  echo "  have : Module.Finite C B := Module.Finite.of_restrictScalars_finite A C B"
  echo "  exact TDifferent.herbrand_quotient A C B r hr v"
  echo "end PkgI6"
  echo
  echo "/-! scratch/swan/Swan.lean -/"
  tail -n +2 Swan.lean | grep -v "^#print axioms"
  echo "end"
  echo
  echo "/-! scratch/swan/Bridge.lean -/"
  tail -n +3 Bridge.lean | grep -v "^#print axioms"
  echo "end"
  echo
  cat final_part.lean
} > All.lean
