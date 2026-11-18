import ExtendedRingMapsV003
import NormalizationCoreV002
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Flatness of the actual local map and finite freeness of the normalization -/

noncomputable section
set_option autoImplicit false

namespace FiniteExtensionValuation

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- The injective local map from the original DVR to the selected valuation ring
is faithfully flat, without any separability or finite-normalization assumption. -/
theorem extended_faithfullyFlat (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O) :
    letI := extensionRingAlgebra O w hw
    Module.FaithfullyFlat O w := by
  letI := extensionRingAlgebra O w hw
  haveI : Module.IsTorsionFree O w :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (baseHom_injective O w hw)
  haveI : Module.Flat O w := inferInstance
  haveI : IsLocalHom (algebraMap O w) := baseHom_isLocalHom O w hw
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- Finite freeness and the degree formula are produced for the whole separable
normalization. Neither a basis nor a finiteness premise is supplied by the caller. -/
theorem finite_separable_normalization_free_rank [FiniteDimensional K M]
    [Algebra.IsSeparable K M] (O : ValuationSubring K) [IsDiscreteValuationRing O] :
    letI := extensionFieldAlgebra (M := M) O
    Module.Free O (integralClosure O M) ∧
      Module.finrank O (integralClosure O M) = Module.finrank K M := by
  letI := extensionFieldAlgebra (M := M) O
  letI := extensionField_tower (M := M) O
  haveI : Module.IsTorsionFree O M := .trans_faithfulSMul O K M
  exact ⟨IsIntegralClosure.module_free O K M (integralClosure O M),
    IsIntegralClosure.rank O K M (integralClosure O M)⟩

universe u

/-- Faithful flatness is bound to the actual native scheme map. -/
theorem spec_extended_flat_surjective {K M : Type u} [Field K] [Field M] [Algebra K M]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O) :
    AlgebraicGeometry.Flat (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (baseHom O w hw))) ∧
      AlgebraicGeometry.Surjective (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (baseHom O w hw))) := by
  letI := extensionRingAlgebra O w hw
  letI := extended_faithfullyFlat O w hw
  apply (AlgebraicGeometry.flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (baseHom O w hw))).2
  change Module.FaithfullyFlat O w
  infer_instance

end FiniteExtensionValuation
