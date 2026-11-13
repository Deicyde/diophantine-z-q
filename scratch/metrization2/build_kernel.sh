#!/bin/bash
# Kernel-world check: Kernel.lean imports ZInQKernel.HDecomp.LeafPush2.T (so `AbVar` = PkgI3.AbVar,
# GroupModel/evalAt/jacDet = ZInQKernel/HDecomp/Faltings/Models.lean, T35 = the kernel's
# ZInQ.LeafPush2.UniformizationExists) and appends:
#  * metrization's part_g0dim.lean (verbatim; Mathlib-only, for G0Dim.dim_baseChange);
#  * metrization's statements AnalyticUniformizationOfDim, JacDetNondegenerate (part_exists.lean
#    l. 17-57) and ProductLocalStructure (part_produnif2.lean l. 14-39), verbatim;
#  * metrization's lemmas of part_jacgerm.lean l. 1-151 and evalAt_mul (part_jacscalar.lean l. 14-22);
#  * this task's parts (part_nondeg3's last theorem, which needs metrization's MetrizedModel
#    assembly, is cut).
# The only edits: `open PkgI3 (AbVar)` after the `open` lines (as in the kernel's Models.lean).
# Prerequisite: lake build ZInQKernel.HDecomp.LeafPush2.T
cd "$(dirname "$0")"
AB='open PkgI3 (AbVar)'
{ echo "import ZInQKernel.HDecomp.LeafPush2.T"
  echo
  cat base/part_g0dim.lean
  echo
  echo "namespace ZInQ.Metrization"
  echo "open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj"
  echo "open NumberField ZInQ.DefFaltings"
  echo "$AB"
  sed -n 17,57p base/part_exists.lean
  sed -n 14,39p base/part_produnif2.lean
  echo "end ZInQ.Metrization"
  echo
  sed -n 1,151p base/part_jacgerm.lean | sed "s/^open NumberField DefFaltings Topology$/open NumberField DefFaltings Topology\n$AB/"
  echo "section Scalar0"
  echo "variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]"
  echo "variable (𝒢 : GroupModel A L)"
  sed -n 14,22p base/part_jacscalar.lean
  echo "end Scalar0"
  echo "end ZInQ.Metrization"
  echo
  for f in part_nondeg1 part_nondeg2; do
    sed -e "s/^open NumberField ZInQ.DefFaltings ZInQ.Metrization Topology$/open NumberField ZInQ.DefFaltings ZInQ.Metrization Topology\n$AB/" -e '/^#print axioms/d' $f.lean
  done
  sed -e "s/^open NumberField ZInQ.DefFaltings ZInQ.Metrization Topology$/open NumberField ZInQ.DefFaltings ZInQ.Metrization Topology\n$AB/" -e '/^#print axioms/d' part_nondeg3.lean \
    | sed '/^\/-- `MetrizationExists` with `JacDetNondegenerate` replaced/,/^  metrizationExists_of. hH hU (jacDetNondegenerate_of hML)$/d'
  sed -e "s/^open NumberField ZInQ.DefFaltings ZInQ.LeafPush2$/open NumberField ZInQ.DefFaltings ZInQ.LeafPush2\n$AB/" -e '/^#print axioms/d' part_unif1.lean
  for f in part_pml1 part_pml2; do sed -e '/^#print axioms/d' $f.lean; done
  sed -e "s/^open NumberField ZInQ.DefFaltings$/open NumberField ZInQ.DefFaltings\n$AB/" -e '/^#print axioms/d' part_pml3.lean
  echo
  echo "#print axioms ZInQ.Metrization2.jacDetNondegenerate"
  echo "#print axioms ZInQ.Metrization2.productLocalStructure"
  echo "#print axioms ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists"
} > Kernel.lean
