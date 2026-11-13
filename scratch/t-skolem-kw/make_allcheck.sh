#!/bin/sh
# Concatenate the four proof files under the imports of scratch/h-decomposition/Leaves.lean.
D=scratch/t-skolem-kw
{
  echo "import Mathlib"
  # JHeight needs the upstream ZInQ oleans (not built here); HeightConstant only
  echo "import ZInQKernel.Compiler.Precision.HeightConstant"
  for f in SkolemNoether BrauerNesbitt FrobeniusDense KroneckerWeberUse; do
    echo
    echo "-- ===== $f.lean ====="
    grep -v '^import ' $D/$f.lean | grep -v '^#print'
  done
  echo
  echo "#print axioms TSkolemKW.skolemNoether"
  echo "#print axioms TSkolemKW.leafSkolemNoether"
  echo "#print axioms TSkolemKW.brauerNesbittChar0"
  echo "#print axioms TSkolemKW.hsynBrauerNesbitt"
  echo "#print axioms TSkolemKW.HS.frobeniusDense_of_chebotarev"
  echo "#print axioms TSkolemKW.KW.eq_of_agree_on_roots"
} > $D/AllCheck.lean
