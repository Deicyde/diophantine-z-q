import ZInQKernel.OneProof.H.TailR
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.RingTheory.Smooth.RegularLocalRing

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem regularSmoothPerfect_proof : CurveSplit.RegularSmoothPerfect := by
  intro k _ _ S _ _ _ q _ hreg
  have : Algebra.FinitePresentation k S := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : IsRegularLocalRing (Localization.AtPrime q) := hreg
  have : Algebra.EssFiniteType k (IsLocalRing.ResidueField (Localization.AtPrime q)) :=
    inferInstanceAs (Algebra.EssFiniteType k (Localization.AtPrime q ⧸ _))
  have : Algebra.IsSmoothAt k q := Algebra.FormallySmooth.localization_of_isRegularLocalRing q
  exact Algebra.IsSmoothAt.exists_notMem_smooth k q

#print axioms regularSmoothPerfect_proof
