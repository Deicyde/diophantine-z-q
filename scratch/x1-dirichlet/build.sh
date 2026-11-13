#!/bin/bash
# Assemble Connect.lean = copy of scratch/g0-mod-newform/NewForm.lean (newform_src.lean, its
# `#print axioms` lines dropped) + two imports + the body of Dirichlet.lean + part_connect.lean.
cd "$(dirname "$0")"
{
  grep '^import' newform_src.lean
  echo "import ZInQKernel.HDecomp.ModCurves.X1Belyi"
  echo "import ZInQKernel.HDecomp.Textbook.KroneckerWeberUse"
  echo
  echo "/-! Copied from scratch/g0-mod-newform/NewForm.lean (compiled there), imports moved up,"
  echo "#print lines dropped. -/"
  grep -v '^#print axioms' newform_src.lean | grep -v '^import' 
  echo
  echo "/-! Copied from scratch/x1-dirichlet/Dirichlet.lean (body, compiled there). -/"
  echo "section DirichletCopy"
  sed -n '/^noncomputable section$/,/^end X1Dirichlet$/p' Dirichlet.lean
  echo "end"
  echo "end DirichletCopy"
  cat part_connect.lean
} > Connect.lean
