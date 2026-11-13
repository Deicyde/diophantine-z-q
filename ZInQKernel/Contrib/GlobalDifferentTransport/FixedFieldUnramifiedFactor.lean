/-
# The actual unramified/total-ramification fixed-field factor

For `E=M^(D∩H)`, put `U=M^(I⊔(D∩H))`. Inertia is normal inside the actual
decomposition group. Its finite subgroup product identity supplies the residue
comparison; no cyclic-quotient or local arithmetic theorem is taken as an input.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.FixedFieldTransport

/-!
# The U part of the actual fixed-field scaffold

All fields and prime contractions are actual fixed fields and inclusions.
`U/F` is proved unramified at the selected prime and `E/U` has residue degree
one. The proofs use global subgroup identities and the pinned ideal tower laws.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open NumberField IntermediateField
open scoped NumberField Pointwise GlobalDifferentTransportFixedFieldTower

namespace GlobalDifferentTransport

/-- The subgroup cutting out the actual selected unramified factor. -/
abbrev unramifiedFactorSubgroup (M : Type*) [Field M] [NumberField M]
    (P : Ideal (𝓞 M)) (H : Subgroup Gal(M/ℚ)) : Subgroup Gal(M/ℚ) :=
  selectedInertiaSubgroup M P ⊔ relativeDecompositionSubgroup M P H

/-- The actual field `U=M^(I⊔(D∩H))`, not an assumed unramified extension. -/
abbrev unramifiedFactorFixedField (M : Type*) [Field M] [NumberField M]
    (P : Ideal (𝓞 M)) (H : Subgroup Gal(M/ℚ)) : IntermediateField ℚ M :=
  fixedField (unramifiedFactorSubgroup M P H)

variable (M : Type*) [Field M] [NumberField M] (P : Ideal (𝓞 M)) (H : Subgroup Gal(M/ℚ))

/-- Both generators of the unramified-factor subgroup lie in the actual decomposition group. -/
theorem unramifiedFactorSubgroup_le_decomposition :
    unramifiedFactorSubgroup M P H ≤ selectedDecompositionSubgroup M P :=
  sup_le (Ideal.inertia_le_stabilizer P) inf_le_left

/-- The actual decomposition field lies in the actual unramified factor. -/
theorem decompositionFixedField_le_unramifiedFactor :
    decompositionFixedField M P ≤ unramifiedFactorFixedField M P H :=
  fixedField_le (unramifiedFactorSubgroup_le_decomposition M P H)

/-- The actual unramified factor lies in the actual transported field. -/
theorem unramifiedFactor_le_transported :
    unramifiedFactorFixedField M P H ≤ transportedFixedField M P H :=
  fixedField_le le_sup_right

/-- The canonical inclusion from the actual decomposition field to its factor field. -/
@[reducible]
def decompositionToUnramifiedFactorAlgebra :
    Algebra (decompositionFixedField M P) (unramifiedFactorFixedField M P H) :=
  (IntermediateField.inclusion (decompositionFixedField_le_unramifiedFactor M P H)).toRingHom.toAlgebra

/-- The canonical inclusion from the actual factor field to the actual transported field. -/
@[reducible]
def unramifiedFactorToTransportedAlgebra :
    Algebra (unramifiedFactorFixedField M P H) (transportedFixedField M P H) :=
  (IntermediateField.inclusion (unramifiedFactor_le_transported M P H)).toRingHom.toAlgebra

scoped[GlobalDifferentTransportFixedFieldTower] attribute [instance 50]
  GlobalDifferentTransport.decompositionToUnramifiedFactorAlgebra
  GlobalDifferentTransport.unramifiedFactorToTransportedAlgebra

/-- The actual factor-to-transported inclusion agrees with the ambient field embedding. -/
theorem unramifiedFactorTransportedIsScalarTower :
    IsScalarTower (unramifiedFactorFixedField M P H) (transportedFixedField M P H) M :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The actual decomposition-to-factor inclusion agrees with the ambient field embedding. -/
theorem decompositionUnramifiedFactorIsScalarTower :
    IsScalarTower (decompositionFixedField M P) (unramifiedFactorFixedField M P H) M :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The rational action agrees with the actual decomposition-to-factor inclusion. -/
theorem rationalDecompositionUnramifiedFactorIsScalarTower :
    IsScalarTower ℚ (decompositionFixedField M P) (unramifiedFactorFixedField M P H) :=
  IsScalarTower.of_algHom
    (IntermediateField.inclusion (decompositionFixedField_le_unramifiedFactor M P H))

/-- The rational action agrees with the actual factor-to-transported inclusion. -/
theorem rationalUnramifiedFactorTransportedIsScalarTower :
    IsScalarTower ℚ (unramifiedFactorFixedField M P H) (transportedFixedField M P H) :=
  IsScalarTower.of_algHom (IntermediateField.inclusion (unramifiedFactor_le_transported M P H))

/-- The complete actual F/U/E tower is compatible, not three unrelated algebra structures. -/
theorem decompositionUnramifiedTransportedIsScalarTower :
    IsScalarTower (decompositionFixedField M P) (unramifiedFactorFixedField M P H)
      (transportedFixedField M P H) := IsScalarTower.of_algebraMap_eq' rfl

scoped[GlobalDifferentTransportFixedFieldTower] attribute [instance]
  GlobalDifferentTransport.unramifiedFactorTransportedIsScalarTower
  GlobalDifferentTransport.decompositionUnramifiedFactorIsScalarTower
  GlobalDifferentTransport.rationalDecompositionUnramifiedFactorIsScalarTower
  GlobalDifferentTransport.rationalUnramifiedFactorTransportedIsScalarTower
  GlobalDifferentTransport.decompositionUnramifiedTransportedIsScalarTower

/-- Inertia is normal inside the actual decomposition group. This is the actual ideal-inertia
normality, not normality of inertia in the whole global Galois group. -/
theorem inertia_subgroupOf_decomposition_normal :
    ((selectedInertiaSubgroup M P).subgroupOf (selectedDecompositionSubgroup M P)).Normal := by
  have h : (selectedInertiaSubgroup M P).subgroupOf (selectedDecompositionSubgroup M P) =
      P.inertia (selectedDecompositionSubgroup M P) := by
    ext σ
    rfl
  rw [h]
  infer_instance

/-- A normal factor's product identity, derived from the existing relative-index formulas. -/
private theorem card_sup_mul_card_inf_normal {G : Type*} [Group G]
    (N J : Subgroup G) [N.Normal] :
    Nat.card (N ⊔ J : Subgroup G) * Nat.card (N ⊓ J : Subgroup G) = Nat.card N * Nat.card J := by
  have hsup := Subgroup.relIndex_mul_card N (N ⊔ J)
  rw [inf_of_le_left le_sup_left, Subgroup.relIndex_sup_left] at hsup
  calc
    Nat.card (N ⊔ J : Subgroup G) * Nat.card (N ⊓ J : Subgroup G) =
        (N.relIndex J * Nat.card N) * Nat.card (N ⊓ J : Subgroup G) := by rw [hsup]
    _ = Nat.card N * (N.relIndex J * Nat.card (N ⊓ J : Subgroup G)) := by ring
    _ = Nat.card N * Nat.card J := by rw [Subgroup.relIndex_mul_card]

/-- The actual inertia/relative-decomposition product identity, proved inside the decomposition
group where inertia is normal and then transported through its injective subtype map. -/
theorem card_unramifiedFactor_mul_card_inter :
    Nat.card (unramifiedFactorSubgroup M P H) *
        Nat.card (selectedInertiaSubgroup M P ⊓ relativeDecompositionSubgroup M P H : Subgroup Gal(M/ℚ)) =
      Nat.card (selectedInertiaSubgroup M P) * Nat.card (relativeDecompositionSubgroup M P H) := by
  let D := selectedDecompositionSubgroup M P
  let I := selectedInertiaSubgroup M P
  let H0 := relativeDecompositionSubgroup M P H
  let N := I.subgroupOf D
  let J := H0.subgroupOf D
  have hI : I ≤ D := Ideal.inertia_le_stabilizer P
  have hH0 : H0 ≤ D := inf_le_left
  let : N.Normal := inertia_subgroupOf_decomposition_normal M P
  have hsup : (N ⊔ J).map D.subtype = I ⊔ H0 := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hI, Subgroup.map_subgroupOf_eq_of_le hH0]
  have hcardSup : Nat.card (N ⊔ J : Subgroup D) = Nat.card (I ⊔ H0 : Subgroup Gal(M/ℚ)) := by
    rw [← hsup]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).toEquiv
  have hcardN : Nat.card N = Nat.card I :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hI).toEquiv
  have hcardJ : Nat.card J = Nat.card H0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH0).toEquiv
  have hcardInf : Nat.card (N ⊓ J : Subgroup D) = Nat.card (I ⊓ H0 : Subgroup Gal(M/ℚ)) := by
    have hinf : N ⊓ J = (I ⊓ H0 : Subgroup Gal(M/ℚ)).subgroupOf D := by
      ext σ
      rfl
    rw [hinf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hI)).toEquiv
  have h := card_sup_mul_card_inf_normal N J
  rw [hcardSup, hcardN, hcardJ, hcardInf] at h
  exact h

variable [IsGalois ℚ M] [P.IsPrime]

/-- The actual factor field is the intersection of E with the actual inertia fixed field. -/
theorem unramifiedFactor_eq_intersection :
    unramifiedFactorFixedField M P H =
      transportedFixedField M P H ⊓ fixedField (selectedInertiaSubgroup M P) := by
  apply IsGalois.fixedField_eq_iff_fixingSubgroup_eq.mpr
  have h := congrArg OrderDual.ofDual
    ((IsGalois.intermediateFieldEquivSubgroup (F := ℚ) (E := M)).map_inf
      (transportedFixedField M P H) (fixedField (selectedInertiaSubgroup M P)))
  change (transportedFixedField M P H ⊓ fixedField (selectedInertiaSubgroup M P)).fixingSubgroup =
    (transportedFixedField M P H).fixingSubgroup ⊔
      (fixedField (selectedInertiaSubgroup M P)).fixingSubgroup at h
  simpa only [transportedFixedField, fixingSubgroup_fixedField, sup_comm] using h

/-- The ambient-prime ramification over F and U is the same because both fix fields containing
the entire actual inertia subgroup. -/
theorem ambient_ramificationIdx_decomposition_eq_unramifiedFactor :
    P.ramificationIdx (𝓞 (decompositionFixedField M P)) =
      P.ramificationIdx (𝓞 (unramifiedFactorFixedField M P H)) := by
  change P.ramificationIdx (𝓞 ↥(fixedField (selectedDecompositionSubgroup M P))) = _
  rw [ramificationIdx_fixedField_eq_card_inf M (selectedDecompositionSubgroup M P) P,
    ramificationIdx_fixedField_eq_card_inf M (unramifiedFactorSubgroup M P H) P,
    inf_of_le_left (Ideal.inertia_le_stabilizer P), inf_of_le_left le_sup_left]

/-- The actual factor prime is globally unramified over the actual decomposition field. -/
theorem unramifiedFactorPrime_ramificationIdx_decomposition_eq_one :
    (P.under (𝓞 (unramifiedFactorFixedField M P H))).ramificationIdx
      (𝓞 (decompositionFixedField M P)) = 1 := by
  let U := unramifiedFactorFixedField M P H
  let F := decompositionFixedField M P
  let : Module.Finite (𝓞 U) (𝓞 M) := Module.Finite.right ℤ (𝓞 U) (𝓞 M)
  apply Nat.eq_of_mul_eq_mul_right (P.ramificationIdx_pos (𝓞 U))
  calc
    (P.under (𝓞 U)).ramificationIdx (𝓞 F) * P.ramificationIdx (𝓞 U) =
        P.ramificationIdx (𝓞 F) := (Ideal.ramificationIdx_tower (R := 𝓞 F) (P.under (𝓞 U)) P).symm
    _ = P.ramificationIdx (𝓞 U) := ambient_ramificationIdx_decomposition_eq_unramifiedFactor M P H
    _ = 1 * P.ramificationIdx (𝓞 U) := (one_mul _).symm

/-- The ambient-prime residue degree over U and E is equal, by the actual inertia-normal product
identity and the global ramification/decomposition cardinalities. -/
theorem ambient_inertiaDeg_unramifiedFactor_eq_transported :
    P.inertiaDeg (𝓞 (unramifiedFactorFixedField M P H)) =
      P.inertiaDeg (𝓞 (transportedFixedField M P H)) := by
  let U := unramifiedFactorFixedField M P H
  let E := transportedFixedField M P H
  let I := selectedInertiaSubgroup M P
  let H0 := relativeDecompositionSubgroup M P H
  have heU : P.ramificationIdx (𝓞 U) = Nat.card I := by
    rw [ramificationIdx_fixedField_eq_card_inf M (unramifiedFactorSubgroup M P H) P,
      inf_of_le_left le_sup_left]
  have heE : P.ramificationIdx (𝓞 E) = Nat.card (I ⊓ H0 : Subgroup Gal(M/ℚ)) :=
    ramificationIdx_fixedField_eq_card_inf M H0 P
  have hdU : P.ramificationIdx (𝓞 U) * P.inertiaDeg (𝓞 U) =
      Nat.card (unramifiedFactorSubgroup M P H) := by
    rw [ramificationIdx_mul_inertiaDeg_fixedField_eq_card_inf M (unramifiedFactorSubgroup M P H) P,
      inf_of_le_right (unramifiedFactorSubgroup_le_decomposition M P H)]
  have hdE : P.ramificationIdx (𝓞 E) * P.inertiaDeg (𝓞 E) = Nat.card H0 := by
    rw [ramificationIdx_mul_inertiaDeg_fixedField_eq_card_inf M H0 P, inf_of_le_right inf_le_left]
  have h := card_unramifiedFactor_mul_card_inter M P H
  rw [← heU, ← heE, ← hdU, ← hdE] at h
  have hproducts : P.ramificationIdx (𝓞 U) *
      (P.ramificationIdx (𝓞 E) * P.inertiaDeg (𝓞 U)) =
      P.ramificationIdx (𝓞 U) * (P.ramificationIdx (𝓞 E) * P.inertiaDeg (𝓞 E)) := by
    calc
      _ = (P.ramificationIdx (𝓞 U) * P.inertiaDeg (𝓞 U)) * P.ramificationIdx (𝓞 E) := by ring
      _ = _ := h
  let : Module.Finite (𝓞 U) (𝓞 M) := Module.Finite.right ℤ (𝓞 U) (𝓞 M)
  let : Module.Finite (𝓞 E) (𝓞 M) := Module.Finite.right ℤ (𝓞 E) (𝓞 M)
  have hcancel := mul_left_cancel₀ (P.ramificationIdx_pos (𝓞 U)).ne' hproducts
  exact mul_left_cancel₀ (P.ramificationIdx_pos (𝓞 E)).ne' hcancel

/-- The actual transported prime has residue degree one over the actual unramified factor. -/
theorem transportedPrime_inertiaDeg_unramifiedFactor_eq_one :
    (P.under (𝓞 (transportedFixedField M P H))).inertiaDeg
      (𝓞 (unramifiedFactorFixedField M P H)) = 1 := by
  let U := unramifiedFactorFixedField M P H
  let E := transportedFixedField M P H
  let : Module.Finite (𝓞 E) (𝓞 M) := Module.Finite.right ℤ (𝓞 E) (𝓞 M)
  apply Nat.eq_of_mul_eq_mul_right (P.inertiaDeg_pos (𝓞 E))
  calc
    (P.under (𝓞 E)).inertiaDeg (𝓞 U) * P.inertiaDeg (𝓞 E) =
        P.inertiaDeg (𝓞 U) := (Ideal.inertiaDeg_tower (R := 𝓞 U) (P.under (𝓞 E)) P).symm
    _ = P.inertiaDeg (𝓞 E) := ambient_inertiaDeg_unramifiedFactor_eq_transported M P H
    _ = 1 * P.inertiaDeg (𝓞 E) := (one_mul _).symm

/-- The actual factor field is unramified at its contracted prime over F. -/
theorem unramifiedFactorPrime_isUnramifiedAt_decomposition :
    Algebra.IsUnramifiedAt (𝓞 (decompositionFixedField M P))
      (P.under (𝓞 (unramifiedFactorFixedField M P H))) :=
  Ideal.ramificationIdx_eq_one_iff.mp (unramifiedFactorPrime_ramificationIdx_decomposition_eq_one M P H)

/-- The actual factor field has a unique prime above the selected F-prime, derived from the
ambient decomposition-field unique-prime theorem. -/
theorem unramifiedFactorFixedField_primesOver :
    Ideal.primesOver (P.under (𝓞 (decompositionFixedField M P)))
      (𝓞 (unramifiedFactorFixedField M P H)) = {P.under (𝓞 (unramifiedFactorFixedField M P H))} := by
  let F := decompositionFixedField M P
  let U := unramifiedFactorFixedField M P H
  exact primesOver_unique_descends (R := 𝓞 F) (S := 𝓞 U) (T := 𝓞 M)
    (P.under (𝓞 F)) P (decompositionFixedField_primesOver M P)

end GlobalDifferentTransport
