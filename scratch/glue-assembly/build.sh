#!/bin/bash
# Concatenate the parts into one checkable file GlueAssembly.lean.
cd "$(dirname "$0")"
{
  echo "import Mathlib"
  echo "import ZInQKernel.Compiler.Precision.HeightConstant"
  echo
  for f in F2 Ext Transfer F4Copy; do grep -v '^import ' $f.lean; echo; done
  cat Assembly.lean
  echo
  echo "#print axioms GlueAssembly.sixContactMinAt_of_glueOutputs"
  echo "#print axioms GlueAssembly.logHeight₁_algebraMap_rat"
  echo "#print axioms GlueAssembly.logHeight_Phi_le"
} > GlueAssembly.lean
