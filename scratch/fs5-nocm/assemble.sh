#!/bin/bash
# Assemble FS5NoCM.lean and FS5Curves.lean from the parts (run from scratch/fs5-nocm/).
set -e
L=$(grep -n "^/-- CM objects of the three kinds" ../qm-pin/QMPin.lean | cut -d: -f1)
( cat part0.lean; sed -n 34,95p ../qm-pin/QMPin.lean; echo; sed -n 507,619p ../qm-pin/QMPin.lean
  printf '\nend AV\n\nend LeafQM\n\n'; cat partB.lean partD.lean partE.lean partG.lean partH.lean partI.lean ) > FS5NoCM.lean
( sed -n 1,2p ../mobius-glue/MobiusGlue.lean
  printf 'import ZInQKernel.HDecomp.Repo.PRArith\nimport ZInQKernel.Hypotheses.JHeight\nimport ZInQKernel.HDecomp.Descent.B1Quat\n'
  sed -n 3,1439p ../mobius-glue/MobiusGlue.lean
  printf '\nnamespace LeafQM\n\nnamespace AV\n\nnamespace Pin\n\nopen CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj\nopen PkgI3\n\n'
  sed -n "${L},617p" ../qm-pin/QMPin.lean
  printf '\nend Pin\n\nend AV\n\nend LeafQM\n\n'
  cat partB.lean partD.lean; sed '/^#print/d' partE.lean; sed '/^#print/d' partG.lean; sed '/^#print/d' partH.lean; sed '/^#print/d' partI.lean; cat partE2.lean ) > FS5Curves.lean
