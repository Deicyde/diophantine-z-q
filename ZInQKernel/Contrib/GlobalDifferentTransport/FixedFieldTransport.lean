/-
# Actual nongalois decomposition-field transport

The original field is `M^H`, the transported field is `M^(D ∩ H)`, and the
base is the actual decomposition fixed field `M^D`. Their inclusions are named
and checked, and `e = f = 1` above the original field follows from genuine
inertia/decomposition intersections and global tower identities.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.FixedFieldPrimeInvariants
public import ZInQKernel.Contrib.GlobalDifferentTransport.UniqueLocalizationTower

/-!
# The F/E part of the actual fixed-field scaffold

No new uniqueness, ramification, residue-degree or different comparison is
assumed. The original intermediate field need not be Galois over `ℚ`.
The ambient number field `M/ℚ` is finite Galois.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open NumberField IntermediateField
open scoped NumberField Pointwise

namespace GlobalDifferentTransport

/-- The actual global decomposition subgroup at the selected integer prime. -/
abbrev selectedDecompositionSubgroup (M : Type*) [Field M] [NumberField M] (P : Ideal (𝓞 M)) :
    Subgroup Gal(M/ℚ) := MulAction.stabilizer Gal(M/ℚ) P

/-- The actual global inertia subgroup at the selected integer prime. -/
abbrev selectedInertiaSubgroup (M : Type*) [Field M] [NumberField M] (P : Ideal (𝓞 M)) :
    Subgroup Gal(M/ℚ) := P.inertia Gal(M/ℚ)

/-- The decomposition subgroup of the original subfield, viewed in the ambient Galois group. -/
abbrev relativeDecompositionSubgroup (M : Type*) [Field M] [NumberField M]
    (P : Ideal (𝓞 M)) (H : Subgroup Gal(M/ℚ)) : Subgroup Gal(M/ℚ) :=
  selectedDecompositionSubgroup M P ⊓ H

/-- The original intermediate field as the actual fixed field of its defining subgroup. -/
abbrev originalFixedField (M : Type*) [Field M] [NumberField M] (H : Subgroup Gal(M/ℚ)) : IntermediateField ℚ M :=
  fixedField H

/-- The actual field transported by adjoining the decomposition fixed field. -/
abbrev transportedFixedField (M : Type*) [Field M] [NumberField M] (P : Ideal (𝓞 M))
    (H : Subgroup Gal(M/ℚ)) : IntermediateField ℚ M :=
  fixedField (relativeDecompositionSubgroup M P H)

variable (M : Type*) [Field M] [NumberField M] (P : Ideal (𝓞 M)) (H : Subgroup Gal(M/ℚ))

/-- The original fixed field lies in the actual transported fixed field. -/
theorem originalFixedField_le_transported : originalFixedField M H ≤ transportedFixedField M P H :=
  fixedField_le inf_le_right

/-- The actual decomposition fixed field lies in the actual transported field. -/
theorem decompositionFixedField_le_transported :
    decompositionFixedField M P ≤ transportedFixedField M P H :=
  fixedField_le inf_le_left

/-- The original-to-transported field algebra is the actual intermediate-field inclusion. -/
@[reducible]
def originalToTransportedAlgebra : Algebra (originalFixedField M H) (transportedFixedField M P H) :=
  (IntermediateField.inclusion (originalFixedField_le_transported M P H)).toRingHom.toAlgebra

/-- The decomposition-to-transported algebra is the actual intermediate-field inclusion. -/
@[reducible]
def decompositionToTransportedAlgebra :
    Algebra (decompositionFixedField M P) (transportedFixedField M P H) :=
  (IntermediateField.inclusion (decompositionFixedField_le_transported M P H)).toRingHom.toAlgebra

scoped[GlobalDifferentTransportFixedFieldTower] attribute [instance 50]
  GlobalDifferentTransport.originalToTransportedAlgebra
  GlobalDifferentTransport.decompositionToTransportedAlgebra

open scoped GlobalDifferentTransportFixedFieldTower

/-- The original field, transported field and actual ambient field form the inclusion tower. -/
theorem originalTransportedIsScalarTower :
    IsScalarTower (originalFixedField M H) (transportedFixedField M P H) M :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The decomposition field, transported field and actual ambient field form the inclusion tower. -/
theorem decompositionTransportedIsScalarTower :
    IsScalarTower (decompositionFixedField M P) (transportedFixedField M P H) M :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The rational-base inclusion agrees with the original-to-transported inclusion. -/
theorem rationalOriginalTransportedIsScalarTower :
    IsScalarTower ℚ (originalFixedField M H) (transportedFixedField M P H) :=
  IsScalarTower.of_algHom (IntermediateField.inclusion (originalFixedField_le_transported M P H))

/-- The rational-base inclusion agrees with the decomposition-to-transported inclusion. -/
theorem rationalDecompositionTransportedIsScalarTower :
    IsScalarTower ℚ (decompositionFixedField M P) (transportedFixedField M P H) :=
  IsScalarTower.of_algHom (IntermediateField.inclusion (decompositionFixedField_le_transported M P H))

scoped[GlobalDifferentTransportFixedFieldTower] attribute [instance]
  GlobalDifferentTransport.originalTransportedIsScalarTower
  GlobalDifferentTransport.decompositionTransportedIsScalarTower
  GlobalDifferentTransport.rationalOriginalTransportedIsScalarTower
  GlobalDifferentTransport.rationalDecompositionTransportedIsScalarTower

variable [IsGalois ℚ M]

/-- The actual transported field is exactly the compositum of the original field and the
actual decomposition field, by the finite Galois correspondence. -/
theorem transportedFixedField_eq_compositum :
    transportedFixedField M P H = originalFixedField M H ⊔ decompositionFixedField M P := by
  change fixedField (selectedDecompositionSubgroup M P ⊓ H) =
    fixedField H ⊔ fixedField (selectedDecompositionSubgroup M P)
  apply IsGalois.fixedField_eq_iff_fixingSubgroup_eq.mpr
  rw [fixingSubgroup_sup, fixingSubgroup_fixedField, fixingSubgroup_fixedField, inf_comm]

variable [P.IsPrime]

/-- Inertia meets the relative decomposition subgroup in exactly the original inertia
intersection. The inclusion of inertia in the actual decomposition group is proved in Mathlib. -/
theorem inertia_inter_relativeDecomposition :
    selectedInertiaSubgroup M P ⊓ relativeDecompositionSubgroup M P H =
      selectedInertiaSubgroup M P ⊓ H := by
  rw [relativeDecompositionSubgroup, ← inf_assoc,
    inf_of_le_left (Ideal.inertia_le_stabilizer P)]

/-- The global ramification index of the ambient prime over the original and transported fields
is identical, by the actual inertia intersections. -/
theorem ambient_ramificationIdx_original_eq_transported :
    P.ramificationIdx (𝓞 (originalFixedField M H)) =
      P.ramificationIdx (𝓞 (transportedFixedField M P H)) := by
  rw [ramificationIdx_fixedField_eq_card_inf M H P,
    ramificationIdx_fixedField_eq_card_inf M (relativeDecompositionSubgroup M P H) P,
    inertia_inter_relativeDecomposition M P H]

/-- The actual local-degree products are identical over the original and transported fields. -/
theorem ambient_localDegree_original_eq_transported :
    P.ramificationIdx (𝓞 (originalFixedField M H)) * P.inertiaDeg (𝓞 (originalFixedField M H)) =
      P.ramificationIdx (𝓞 (transportedFixedField M P H)) *
        P.inertiaDeg (𝓞 (transportedFixedField M P H)) := by
  rw [ramificationIdx_mul_inertiaDeg_fixedField_eq_card_inf M H P,
    ramificationIdx_mul_inertiaDeg_fixedField_eq_card_inf M (relativeDecompositionSubgroup M P H) P]
  have hgroup : (selectedDecompositionSubgroup M P ⊓ H) =
      selectedDecompositionSubgroup M P ⊓ relativeDecompositionSubgroup M P H := by
    change (selectedDecompositionSubgroup M P ⊓ H) =
      selectedDecompositionSubgroup M P ⊓ (selectedDecompositionSubgroup M P ⊓ H)
    rw [← inf_assoc, inf_idem]
  rw [hgroup]

/-- The actual residue degree at the ambient prime is unchanged by this field transport. -/
theorem ambient_inertiaDeg_original_eq_transported :
    P.inertiaDeg (𝓞 (originalFixedField M H)) =
      P.inertiaDeg (𝓞 (transportedFixedField M P H)) := by
  let : Module.Finite (𝓞 (transportedFixedField M P H)) (𝓞 M) :=
    Module.Finite.right ℤ (𝓞 (transportedFixedField M P H)) (𝓞 M)
  have h := ambient_localDegree_original_eq_transported M P H
  rw [ambient_ramificationIdx_original_eq_transported M P H] at h
  exact mul_left_cancel₀ (P.ramificationIdx_pos (𝓞 (transportedFixedField M P H))).ne' h

/-- The transported prime over the original field has genuine global ramification index one. -/
theorem transportedPrime_ramificationIdx_original_eq_one :
    (P.under (𝓞 (transportedFixedField M P H))).ramificationIdx (𝓞 (originalFixedField M H)) = 1 := by
  let E := transportedFixedField M P H
  let L := originalFixedField M H
  let : Module.Finite (𝓞 E) (𝓞 M) := Module.Finite.right ℤ (𝓞 E) (𝓞 M)
  apply Nat.eq_of_mul_eq_mul_right (P.ramificationIdx_pos (𝓞 E))
  calc
    (P.under (𝓞 E)).ramificationIdx (𝓞 L) * P.ramificationIdx (𝓞 E) =
        P.ramificationIdx (𝓞 L) := (Ideal.ramificationIdx_tower (R := 𝓞 L) (P.under (𝓞 E)) P).symm
    _ = P.ramificationIdx (𝓞 E) := ambient_ramificationIdx_original_eq_transported M P H
    _ = 1 * P.ramificationIdx (𝓞 E) := (one_mul _).symm

/-- The transported prime over the original field has genuine global residue degree one. -/
theorem transportedPrime_inertiaDeg_original_eq_one :
    (P.under (𝓞 (transportedFixedField M P H))).inertiaDeg (𝓞 (originalFixedField M H)) = 1 := by
  let E := transportedFixedField M P H
  let L := originalFixedField M H
  let : Module.Finite (𝓞 E) (𝓞 M) := Module.Finite.right ℤ (𝓞 E) (𝓞 M)
  apply Nat.eq_of_mul_eq_mul_right (P.inertiaDeg_pos (𝓞 E))
  calc
    (P.under (𝓞 E)).inertiaDeg (𝓞 L) * P.inertiaDeg (𝓞 E) =
        P.inertiaDeg (𝓞 L) := (Ideal.inertiaDeg_tower (R := 𝓞 L) (P.under (𝓞 E)) P).symm
    _ = P.inertiaDeg (𝓞 E) := ambient_inertiaDeg_original_eq_transported M P H
    _ = 1 * P.inertiaDeg (𝓞 E) := (one_mul _).symm

/-- The transported prime is actually unramified over the original field. -/
theorem transportedPrime_isUnramifiedAt_original :
    Algebra.IsUnramifiedAt (𝓞 (originalFixedField M H)) (P.under (𝓞 (transportedFixedField M P H))) :=
  Ideal.ramificationIdx_eq_one_iff.mp (transportedPrime_ramificationIdx_original_eq_one M P H)

/-- The unique-prime property descends from the actual decomposition field to the transported
field. It is not assumed of the original field when primes split. -/
theorem transportedFixedField_primesOver :
    Ideal.primesOver (P.under (𝓞 (decompositionFixedField M P)))
      (𝓞 (transportedFixedField M P H)) = {P.under (𝓞 (transportedFixedField M P H))} := by
  let F := decompositionFixedField M P
  let E := transportedFixedField M P H
  exact primesOver_unique_descends (R := 𝓞 F) (S := 𝓞 E) (T := 𝓞 M)
    (P.under (𝓞 F)) P (decompositionFixedField_primesOver M P)

end GlobalDifferentTransport
