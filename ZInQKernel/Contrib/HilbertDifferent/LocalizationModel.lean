import ZInQKernel.Contrib.GlobalDifferentTransport.DecompositionFieldDifferent
import ZInQKernel.Contrib.HilbertDifferent.Transport

/-!
# The actual localization of the decomposition fixed field

The field and prime are the frozen supplier's `decompositionFixedField` and its
actual contraction. The localized ring map is `algebraOfLiesOver`. Field maps
are exactly the supplier's canonical `IsLocalization.lift` maps, not unrelated
algebra structures. Its unique-prime and module-finiteness results are consumed
without changing their source or introducing a split-prime finiteness premise.

The declared instances are scoped to this concrete model. This module supplies
no Serre bound, completed-different identity, or independent acceptance.
Frozen direct suppliers: DecompositionFieldDifferent.lean
`6acf62d40360fd6e0bc93554148d8dc5bd3a15a7e0579f077155c33112226762`,
CanonicalLocalization.lean
`f27e7ba1de97834a41b7729876469b521d01249efe7865e0cff1f73ff3d9323f`,
FixedFieldLocalization.lean
`2194aa841e0f2190bd3bb5311482923c25af33e6b2d2fde189e382105b3e5d1a`.
-/

noncomputable section

open NumberField
open scoped Pointwise

namespace ZInQ.Contrib.HilbertDifferent.LocalizationModel

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
  (P : Ideal (𝓞 L)) [P.IsPrime]

/-- The already constructed decomposition fixed field. -/
abbrev decompField := GlobalDifferentTransport.decompositionFixedField L P

/-- Its actual prime under the selected global prime. -/
abbrev basePrime := P.under (𝓞 (decompField L P))

/-- The localized decomposition-field integer ring. -/
abbrev baseRing := Localization.AtPrime (basePrime L P)

/-- The original number-field integer ring localized at the actual selected prime. -/
abbrev topRing := Localization.AtPrime P

/-- Exactly the canonical map between the two prime localizations. -/
@[reducible]
def localAlgebra : Algebra (baseRing L P) (topRing L P) :=
  Localization.AtPrime.algebraOfLiesOver (basePrime L P) P

/-- Canonical base-localization embedding into the original fixed field. -/
@[reducible]
def baseFieldAlgebra : Algebra (baseRing L P) (decompField L P) :=
  GlobalDifferentTransport.localizationFractionFieldAlgebra (𝓞 (decompField L P))
    (decompField L P) (basePrime L P).primeCompl
    (basePrime L P).primeCompl_le_nonZeroDivisors

/-- Canonical top-localization embedding into the original number field. -/
@[reducible]
def topFieldAlgebra : Algebra (topRing L P) L :=
  GlobalDifferentTransport.localizationFractionFieldAlgebra (𝓞 L) L P.primeCompl
    P.primeCompl_le_nonZeroDivisors

/-- The localized base acts on the original top field through the actual fixed-field inclusion. -/
@[reducible]
def baseTopFieldAlgebra : Algebra (baseRing L P) L :=
  GlobalDifferentTransport.localizationBaseToExtensionFieldAlgebra
    (𝓞 (decompField L P)) (decompField L P) L (basePrime L P).primeCompl
    (basePrime L P).primeCompl_le_nonZeroDivisors

scoped[HilbertDifferentLocalization] attribute [instance]
  ZInQ.Contrib.HilbertDifferent.LocalizationModel.localAlgebra
  ZInQ.Contrib.HilbertDifferent.LocalizationModel.baseFieldAlgebra
  ZInQ.Contrib.HilbertDifferent.LocalizationModel.topFieldAlgebra
  ZInQ.Contrib.HilbertDifferent.LocalizationModel.baseTopFieldAlgebra

open scoped HilbertDifferentLocalization

/-- The base localization and its original integer ring have the same fraction field. -/
theorem base_isFractionRing : IsFractionRing (baseRing L P) (decompField L P) :=
  GlobalDifferentTransport.isFractionRing_localization_actualField
    (𝓞 (decompField L P)) (decompField L P) (basePrime L P).primeCompl
    (basePrime L P).primeCompl_le_nonZeroDivisors

/-- The top localization has the original number field as fraction field. -/
theorem top_isFractionRing : IsFractionRing (topRing L P) L :=
  GlobalDifferentTransport.isFractionRing_localization_actualField (𝓞 L) L P.primeCompl
    P.primeCompl_le_nonZeroDivisors

/-- The canonical base lift extends its original integer-ring map. -/
theorem base_integer_field_tower :
    IsScalarTower (𝓞 (decompField L P)) (baseRing L P) (decompField L P) :=
  GlobalDifferentTransport.localizationFractionFieldIsScalarTower
    (𝓞 (decompField L P)) (decompField L P) (basePrime L P).primeCompl
    (basePrime L P).primeCompl_le_nonZeroDivisors

/-- The canonical top lift extends the original integer-ring inclusion. -/
theorem top_integer_field_tower : IsScalarTower (𝓞 L) (topRing L P) L :=
  GlobalDifferentTransport.localizationFractionFieldIsScalarTower (𝓞 L) L P.primeCompl
    P.primeCompl_le_nonZeroDivisors

/-- The base lift and fixed-field inclusion give the same top-field action. -/
theorem base_field_top_tower : IsScalarTower (baseRing L P) (decompField L P) L :=
  GlobalDifferentTransport.localizationBaseFieldIsScalarTower
    (𝓞 (decompField L P)) (decompField L P) L (basePrime L P).primeCompl
    (basePrime L P).primeCompl_le_nonZeroDivisors

/-- The original base, its localization and the original top field commute. -/
theorem base_integer_top_tower :
    IsScalarTower (𝓞 (decompField L P)) (baseRing L P) L :=
  GlobalDifferentTransport.localizationBaseToExtensionFieldIsScalarTower
    (𝓞 (decompField L P)) (decompField L P) L (basePrime L P).primeCompl
    (basePrime L P).primeCompl_le_nonZeroDivisors

scoped[HilbertDifferentLocalization] attribute [instance]
  ZInQ.Contrib.HilbertDifferent.LocalizationModel.base_isFractionRing
  ZInQ.Contrib.HilbertDifferent.LocalizationModel.top_isFractionRing
  ZInQ.Contrib.HilbertDifferent.LocalizationModel.base_integer_field_tower
  ZInQ.Contrib.HilbertDifferent.LocalizationModel.top_integer_field_tower
  ZInQ.Contrib.HilbertDifferent.LocalizationModel.base_field_top_tower
  ZInQ.Contrib.HilbertDifferent.LocalizationModel.base_integer_top_tower

/-- The actual localized square agrees with the two canonical field embeddings. -/
theorem base_top_field_tower : IsScalarTower (baseRing L P) (topRing L P) L :=
  IsScalarTower.of_algebraMap_eq'
    (GlobalDifferentTransport.NumberFieldLocalization.atPrime_fractionField_square
      (decompField L P) L (basePrime L P) P).symm

/-- The original fixed-field integers act through the same top-localization inclusion. -/
theorem base_integer_local_top_tower :
    IsScalarTower (𝓞 (decompField L P)) (topRing L P) L :=
  IsScalarTower.to₁₃₄ (𝓞 (decompField L P)) (𝓞 L) (topRing L P) L

scoped[HilbertDifferentLocalization] attribute [instance]
  ZInQ.Contrib.HilbertDifferent.LocalizationModel.base_top_field_tower
  ZInQ.Contrib.HilbertDifferent.LocalizationModel.base_integer_local_top_tower

/-- Injectivity of the actual localized ring map follows from the commuting fraction-field square. -/
theorem local_faithful : FaithfulSMul (baseRing L P) (topRing L P) :=
  FaithfulSMul.of_field_isFractionRing (baseRing L P) (topRing L P) (decompField L P) L

scoped[HilbertDifferentLocalization] attribute [instance]
  ZInQ.Contrib.HilbertDifferent.LocalizationModel.local_faithful

/-- Torsion-freeness is derived from the injective canonical localized map. -/
theorem local_isTorsionFree : Module.IsTorsionFree (baseRing L P) (topRing L P) :=
  inferInstance

/-- The frozen unique-prime result gives genuine local module-finiteness. -/
theorem local_moduleFinite : Module.Finite (baseRing L P) (topRing L P) :=
  GlobalDifferentTransport.decompositionFixedField_moduleFinite_localization L P

/-- The top localization is exactly the simultaneous localization at the actual base complement. -/
theorem top_isBaseLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid (𝓞 L) (basePrime L P).primeCompl) (topRing L P) :=
  GlobalDifferentTransport.decompositionFixedField_isLocalization L P

scoped[HilbertDifferentLocalization] attribute [instance]
  ZInQ.Contrib.HilbertDifferent.LocalizationModel.local_isTorsionFree
  ZInQ.Contrib.HilbertDifferent.LocalizationModel.local_moduleFinite
  ZInQ.Contrib.HilbertDifferent.LocalizationModel.top_isBaseLocalization

/-- Actual integral closure inside the unchanged original top field follows from the proved
simultaneous-localization supplier and the actual unique-prime fibre. -/
theorem local_integralClosure : IsIntegralClosure (topRing L P) (baseRing L P) L :=
  GlobalDifferentTransport.isIntegralClosure_baseLocalization
    (R := 𝓞 (decompField L P)) (Rₘ := baseRing L P)
    (S := 𝓞 L) (Sₘ := topRing L P) (K := decompField L P) (L := L)
    (M := (basePrime L P).primeCompl) (basePrime L P).primeCompl_le_nonZeroDivisors

/-- The original field over the actual decomposition fixed field is finite and Galois. -/
theorem field_isGalois : IsGalois (decompField L P) L :=
  IsGalois.of_fixed_field L (MulAction.stabilizer Gal(L/ℚ) P)

scoped[HilbertDifferentLocalization] attribute [instance]
  ZInQ.Contrib.HilbertDifferent.LocalizationModel.local_integralClosure
  ZInQ.Contrib.HilbertDifferent.LocalizationModel.field_isGalois

/-- The selected nonzero prime gives DVRs on both sides of the actual localized map. -/
theorem localizations_areDVR (hP : P ≠ ⊥) :
    IsDiscreteValuationRing (baseRing L P) ∧ IsDiscreteValuationRing (topRing L P) :=
  GlobalDifferentTransport.decompositionFixedField_localizations_areDVR L P hP

/-- The localized base residue field is finite, hence perfect, at the actual nonzero prime. -/
theorem base_residue_finite (hP : P ≠ ⊥) : Finite (IsLocalRing.ResidueField (baseRing L P)) := by
  let : (basePrime L P).IsMaximal := (inferInstance : (basePrime L P).IsPrime).isMaximal
    (GlobalDifferentTransport.decompositionFixedField_under_ne_bot L P hP)
  change Finite (basePrime L P).ResidueField
  infer_instance

/-- Perfectness needed by the monogenic supplier is proved from the actual finite residue field. -/
theorem base_residue_perfect (hP : P ≠ ⊥) :
    PerfectField (IsLocalRing.ResidueField (baseRing L P)) := by
  let := base_residue_finite L P hP
  infer_instance

end ZInQ.Contrib.HilbertDifferent.LocalizationModel
