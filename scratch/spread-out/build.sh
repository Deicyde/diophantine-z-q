#!/bin/bash
# Assemble SpreadOut.lean = import lines + part_n1.lean + #print axioms.
# Check (from the repository root): lake env lean scratch/spread-out/SpreadOut.lean
cd "$(dirname "$0")"
{
  echo "import ZInQKernel.HDecomp.Faltings.H5BaseChange"
  echo "import ZInQKernel.Contrib.SpreadOut.NumberField"
  echo
  cat part_n1.lean
  echo
  echo "#print axioms ZInQ.SpreadOutN1.abVarSpreadsOut_of_ega"
  echo "#print axioms ZInQ.Contrib.SpreadOut.NF.abVarSpreadsOut_of_ega"
  echo "#print axioms ZInQ.Contrib.SpreadOut.exists_grpObj_descend"
  echo "#print axioms ZInQ.Contrib.SpreadOut.exists_lift"
  echo "#print axioms ZInQ.Contrib.SpreadOut.exists_map_eq"
  echo "#print axioms ZInQ.Contrib.SpreadOut.NF.specConeIsLimit"
  echo "#print axioms ZInQ.Contrib.SpreadOut.isMonHom_descend"
} > SpreadOut.lean
