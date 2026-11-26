import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.JLine
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.Normal
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.TensorProduct.Finite

/-! # The rational quotient over the function field of the j-line -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric

open LeafModCurves
open scoped TensorProduct

variable {N : ℕ} [NeZero N] (h₂ : 2 ≤ N)

/-- Localize the named rational quotient at the generic point of the actual j-line. -/
noncomputable abbrev Y0RationalGenericJ :=
  letI := (Y0RationalJMap h₂).toRingHom.toAlgebra
  Qj ⊗[Polynomial ℚ] Y0RationalAlgebra h₂

/-- The rational short-level ring maps to its generic j-fibre. -/
noncomputable def Y0RationalGenericJInclusion :
    Y0RationalAlgebra h₂ →+* Y0RationalGenericJ h₂ := by
  letI := (Y0RationalJMap h₂).toRingHom.toAlgebra
  exact Algebra.TensorProduct.includeRight.toRingHom

/-- Finiteness over the j-line gives a finite-dimensional algebra over its function field. -/
theorem Y0RationalGenericJ_finite : FiniteDimensional Qj (Y0RationalGenericJ h₂) := by
  letI := (Y0RationalJMap h₂).toRingHom.toAlgebra
  letI := Y0RationalJMap_finite h₂
  exact Module.Finite.base_change (Polynomial ℚ) Qj (Y0RationalAlgebra h₂)

/-- Passing to the generic j-fibre loses no elements of the rational quotient. -/
theorem Y0RationalGenericJInclusion_injective :
    Function.Injective (Y0RationalGenericJInclusion h₂) := by
  letI := (Y0RationalJMap h₂).toRingHom.toAlgebra
  letI := Y0RationalAlgebra_j_torsionFree h₂
  exact Algebra.TensorProduct.includeRight_injective
    (IsFractionRing.injective (Polynomial ℚ) Qj)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The generic j-fibre is reduced by normality of the rational quotient and localization. -/
theorem Y0RationalGenericJ_reduced : IsReduced (Y0RationalGenericJ h₂) := by
  let P := Polynomial ℚ
  let B := Y0RationalAlgebra h₂
  letI := (Y0RationalJMap h₂).toRingHom.toAlgebra
  have hB : IsReduced B := isReduced_ofLocalizationMaximal B fun m hm => by
    letI := hm.isPrime
    let L := Localization.AtPrime m
    have hL : IsDomain L := (Y0RationalAlgebra_normal h₂ m).1
    exact @isReduced_of_noZeroDivisors L _
      (@IsLeftCancelMulZero.to_noZeroDivisors L _ hL.toIsCancelMulZero.toIsLeftCancelMulZero)
  letI : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors P))
      (Y0RationalGenericJ h₂) :=
    (Algebra.isLocalization_iff_isPushout (nonZeroDivisors P) Qj).mpr inferInstance
  exact isReduced_localizationPreserves (Algebra.algebraMapSubmonoid B (nonZeroDivisors P))
    (Y0RationalGenericJ h₂) hB

#print axioms Y0RationalGenericJ
#print axioms Y0RationalGenericJInclusion
#print axioms Y0RationalGenericJ_finite
#print axioms Y0RationalGenericJInclusion_injective
#print axioms Y0RationalGenericJ_reduced

end WeierstrassCurve.ModelLevels.ModelGeneric
