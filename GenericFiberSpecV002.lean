import GenericFiberPushoutV002
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.Ring.Constructions

/-! # Tensor and native scheme descriptions of the actual generic fiber -/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FiniteExtensionValuation

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- Tensoring the actual extended valuation ring with the original fraction field
gives the actual extension field. -/
def genericFiberEquiv [FiniteDimensional K M] (O : ValuationSubring K)
    [IsDiscreteValuationRing O] (w : ValuationSubring M)
    (hw : w.comap (algebraMap K M) = O) :
    letI := extensionRingAlgebra O w hw
    (w ⊗[O] K) ≃ₐ[w] M := by
  letI := extensionRingAlgebra O w hw
  letI := extensionFieldAlgebra (M := M) O
  letI := extensionField_tower (M := M) O
  letI := extensionRing_tower O w hw
  letI := finite_extension_generic_pushout O w hw
  exact Algebra.IsPushout.equiv O w K M

/-- The generic-fiber equivalence is the literal multiplication of the two
actual inclusions, not an arbitrarily supplied identification. -/
theorem genericFiberEquiv_tmul [FiniteDimensional K M] (O : ValuationSubring K)
    [IsDiscreteValuationRing O] (w : ValuationSubring M)
    (hw : w.comap (algebraMap K M) = O) (a : w) (b : K) :
    letI := extensionRingAlgebra O w hw
    genericFiberEquiv O w hw (a ⊗ₜ[O] b) = (a : M) * algebraMap K M b := by
  letI := extensionRingAlgebra O w hw
  letI := extensionFieldAlgebra (M := M) O
  letI := extensionField_tower (M := M) O
  letI := extensionRing_tower O w hw
  letI := finite_extension_generic_pushout O w hw
  exact Algebra.IsPushout.equiv_tmul O w K M a b

universe u

/-- The native spectrum of the extension field is the actual generic-fiber
pullback of the selected valuation ring. No completion is used. -/
theorem spec_generic_fiber_isPullback {K M : Type u} [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O) :
    IsPullback (Spec.map (CommRingCat.ofHom w.subtype))
      (Spec.map (CommRingCat.ofHom (algebraMap K M)))
      (Spec.map (CommRingCat.ofHom (baseHom O w hw)))
      (Spec.map (CommRingCat.ofHom O.subtype)) := by
  letI := extensionRingAlgebra O w hw
  letI := extensionFieldAlgebra (M := M) O
  letI := extensionField_tower (M := M) O
  letI := extensionRing_tower O w hw
  letI := finite_extension_generic_pushout O w hw
  change IsPullback (Spec.map (CommRingCat.ofHom (algebraMap w M)))
    (Spec.map (CommRingCat.ofHom (algebraMap K M)))
    (Spec.map (CommRingCat.ofHom (algebraMap O w)))
    (Spec.map (CommRingCat.ofHom (algebraMap O K)))
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout O w K M)

end FiniteExtensionValuation
