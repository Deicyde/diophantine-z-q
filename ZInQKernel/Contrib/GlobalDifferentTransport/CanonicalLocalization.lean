/-
# Canonical maps from localized rings to their actual fraction fields

These maps are IsLocalization.lift of the given affine-model embeddings. The
commuting square with a simultaneously localized extension is proved from the
localization universal property. No different-image identity is assumed.
-/
module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Algebra

/-!
# Canonical localized fraction-field squares

The named maps extend the actual affine-model embeddings. Their commuting
square constructs all fraction-field scalar towers in the concrete applications.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped nonZeroDivisors

namespace GlobalDifferentTransport

/-- The canonical localized embedding into the original fraction field. -/
def localizationToFractionField (R K : Type*) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (T : Submonoid R) (hT : T ≤ R⁰) :
    Localization T →+* K :=
  IsLocalization.lift (fun t : T ↦
    IsLocalization.map_units (R := R) (M := R⁰) K ⟨(t : R), hT t.2⟩)

/-- The localization acts through its canonical embedding into the original fraction field. -/
@[reducible]
def localizationFractionFieldAlgebra (R K : Type*) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (T : Submonoid R) (hT : T ≤ R⁰) :
    Algebra (Localization T) K :=
  (localizationToFractionField R K T hT).toAlgebra

/-- The localized base acts on the extension field through its canonical base-field embedding. -/
@[reducible]
def localizationBaseToExtensionFieldAlgebra (R K L : Type*)
    [CommRing R] [IsDomain R] [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] (T : Submonoid R) (hT : T ≤ R⁰) : Algebra (Localization T) L :=
  ((algebraMap K L).comp (localizationToFractionField R K T hT)).toAlgebra

section Single

variable (R K : Type*) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (T : Submonoid R) (hT : T ≤ R⁰)

/-- The canonical localized embedding agrees with the original embedding on every affine element. -/
theorem localizationToFractionField_algebraMap (r : R) :
    localizationToFractionField R K T hT (algebraMap R (Localization T) r) =
      algebraMap R K r := IsLocalization.lift_eq _ r

/-- The affine-model square as an equality of actual ring homomorphisms. -/
theorem localizationToFractionField_comp_algebraMap :
    (localizationToFractionField R K T hT).comp (algebraMap R (Localization T)) =
      algebraMap R K := IsLocalization.lift_comp _

/-- The original ring, its localization, and its actual fraction field form a scalar tower. -/
theorem localizationFractionFieldIsScalarTower :
    let _ := localizationFractionFieldAlgebra R K T hT
    IsScalarTower R (Localization T) K := by
  let _ := localizationFractionFieldAlgebra R K T hT
  exact IsScalarTower.of_algebraMap_eq'
    (localizationToFractionField_comp_algebraMap R K T hT).symm

/-- The original fraction field is also the fraction field of the canonically embedded localization. -/
theorem isFractionRing_localization_actualField :
    let _ := localizationFractionFieldAlgebra R K T hT
    IsFractionRing (Localization T) K := by
  let _ := localizationFractionFieldAlgebra R K T hT
  let _ := localizationFractionFieldIsScalarTower R K T hT
  exact IsFractionRing.isFractionRing_of_isLocalization T (Localization T) K hT

end Single

section Extension

variable (R S K L : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Field K] [Field L] [Algebra R S] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  (T : Submonoid R) (hT : T ≤ R⁰)

include K L hT in
omit [IsDomain R] [IsFractionRing S L] in
/-- The actual global field square shows that image denominators are nonzero divisors. -/
theorem imageDenominators_le_nonZeroDivisors : Algebra.algebraMapSubmonoid S T ≤ S⁰ :=
  map_le_nonZeroDivisors_of_injective _
    (algebraMap_injective_of_field_isFractionRing R S K L) hT

/-- The simultaneous-localization square with the original fraction-field embeddings commutes.
Both localized field maps are canonical lifts, not supplied comparison hypotheses. -/
theorem localizationToFractionField_extension_square :
    (localizationToFractionField S L (Algebra.algebraMapSubmonoid S T)
      (imageDenominators_le_nonZeroDivisors R S K L T hT)).comp
        (algebraMap (Localization T) (Localization (Algebra.algebraMapSubmonoid S T))) =
      (algebraMap K L).comp (localizationToFractionField R K T hT) := by
  apply IsLocalization.ringHom_ext T
  apply RingHom.ext
  intro r
  simp only [RingHom.comp_apply]
  have hlocal : algebraMap (Localization T) (Localization (Algebra.algebraMapSubmonoid S T))
      (algebraMap R (Localization T) r) =
      algebraMap S (Localization (Algebra.algebraMapSubmonoid S T)) (algebraMap R S r) := by
    rw [← IsScalarTower.algebraMap_apply R (Localization T),
      IsScalarTower.algebraMap_apply R S]
  rw [hlocal, localizationToFractionField_algebraMap,
    localizationToFractionField_algebraMap,
    ← IsScalarTower.algebraMap_apply R S L, ← IsScalarTower.algebraMap_apply R K L]

/-- The simultaneously localized base and extension and the actual target field form a scalar
tower, by the proved canonical fraction-field square. -/
theorem localizationExtensionFieldIsScalarTower :
    let _ := localizationFractionFieldAlgebra S L (Algebra.algebraMapSubmonoid S T)
      (imageDenominators_le_nonZeroDivisors R S K L T hT)
    let _ := localizationBaseToExtensionFieldAlgebra R K L T hT
    IsScalarTower (Localization T) (Localization (Algebra.algebraMapSubmonoid S T)) L := by
  let _ := localizationFractionFieldAlgebra S L (Algebra.algebraMapSubmonoid S T)
    (imageDenominators_le_nonZeroDivisors R S K L T hT)
  let _ := localizationBaseToExtensionFieldAlgebra R K L T hT
  exact IsScalarTower.of_algebraMap_eq'
    (localizationToFractionField_extension_square R S K L T hT).symm

end Extension

section BaseExtension

variable (R K L : Type*) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  (T : Submonoid R) (hT : T ≤ R⁰)

omit [Algebra R L] [IsScalarTower R K L] in
/-- The localized base, the original base field and the target field form the canonical tower. -/
theorem localizationBaseFieldIsScalarTower :
    let _ := localizationFractionFieldAlgebra R K T hT
    let _ := localizationBaseToExtensionFieldAlgebra R K L T hT
    IsScalarTower (Localization T) K L := by
  let _ := localizationFractionFieldAlgebra R K T hT
  let _ := localizationBaseToExtensionFieldAlgebra R K L T hT
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- The original base, its localization and the target field form the actual scalar tower. -/
theorem localizationBaseToExtensionFieldIsScalarTower :
    let _ := localizationBaseToExtensionFieldAlgebra R K L T hT
    IsScalarTower R (Localization T) L := by
  let _ := localizationBaseToExtensionFieldAlgebra R K L T hT
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap R L r = algebraMap K L
    (localizationToFractionField R K T hT (algebraMap R (Localization T) r))
  rw [localizationToFractionField_algebraMap, IsScalarTower.algebraMap_apply R K L]

end BaseExtension

end GlobalDifferentTransport
