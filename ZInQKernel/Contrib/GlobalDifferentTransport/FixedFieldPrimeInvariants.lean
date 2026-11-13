/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the source LICENSE.
Authors: The Tau Ceti contributors

Declaration-level adaptation from TauCeti revision
 a6027b1d24fcb935c53bd5b50d11b40991cda418,
NumberTheory/NumberField/FixedField.lean, lines 178–240.
Uses Mathlib 4.35's existing subgroupEquivAlgEquiv; no Galois correspondence
proof or local arithmetic is duplicated.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.DecompositionFieldDifferent

/-!
# Actual stabilizer and inertia intersections over fixed fields

The Galois correspondence carries an automorphism without moving its field or
integer-ring elements. Consequently the actual stabilizer and inertia over the
fixed field correspond to intersections with its defining subgroup. Their
cardinalities compute the genuine global prime invariants using pinned Hilbert theory.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open NumberField IntermediateField
open scoped NumberField Pointwise

namespace GlobalDifferentTransport

variable (M : Type*) [Field M] [NumberField M] (H : Subgroup Gal(M/ℚ))

/-- Rebundling an automorphism over its fixed field preserves its action on actual integers. -/
theorem fixedFieldAut_smul_integer (σ : H) (a : 𝓞 M) :
    IntermediateField.subgroupEquivAlgEquiv H σ • a = (σ : Gal(M/ℚ)) • a := by
  apply NumberField.RingOfIntegers.ext
  rfl

/-- Rebundling an automorphism over its fixed field preserves its action on actual ideals. -/
theorem fixedFieldAut_smul_ideal (σ : H) (P : Ideal (𝓞 M)) :
    IntermediateField.subgroupEquivAlgEquiv H σ • P = (σ : Gal(M/ℚ)) • P := by
  rw [Ideal.pointwise_smul_def, Ideal.pointwise_smul_def]
  rfl

/-- The actual decomposition group over a fixed field pulls back to the original stabilizer
inside its defining subgroup. -/
theorem comap_stabilizer_fixedField (P : Ideal (𝓞 M)) :
    (MulAction.stabilizer Gal(M/↥(fixedField H)) P).comap
        (IntermediateField.subgroupEquivAlgEquiv H).toMonoidHom =
      (MulAction.stabilizer Gal(M/ℚ) P).subgroupOf H := by
  ext σ
  simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  exact Eq.congr_left (fixedFieldAut_smul_ideal M H σ P)

/-- The actual inertia over a fixed field pulls back to the original inertia inside its
subgroup. The proof compares each actual integral congruence, not only group names. -/
theorem comap_inertia_fixedField (P : Ideal (𝓞 M)) :
    (P.inertia Gal(M/↥(fixedField H))).comap
        (IntermediateField.subgroupEquivAlgEquiv H).toMonoidHom =
      (P.inertia Gal(M/ℚ)).subgroupOf H := by
  ext σ
  simp only [Subgroup.mem_comap, Ideal.mem_inertia, Subgroup.mem_subgroupOf]
  rfl

/-- The Galois correspondence's actual pulled-back subgroup has the cardinality of the
original intersection, without a hidden index or degree factor. -/
private theorem card_fixedField_subgroup_eq_card_inf
    {A : Subgroup Gal(M/↥(fixedField H))} {B : Subgroup Gal(M/ℚ)}
    (h : A.comap (IntermediateField.subgroupEquivAlgEquiv H).toMonoidHom = B.subgroupOf H) :
    Nat.card A = Nat.card (B ⊓ H : Subgroup Gal(M/ℚ)) := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : B ⊓ H ≤ H)).toEquiv, Subgroup.inf_subgroupOf_right]
  have he (σ : H) : σ ∈ B.subgroupOf H ↔
      (IntermediateField.subgroupEquivAlgEquiv H) σ ∈ A := by
    rw [← h, Subgroup.mem_comap]
    rfl
  exact (Nat.card_congr (Equiv.subtypeEquiv
    (IntermediateField.subgroupEquivAlgEquiv H).toEquiv he)).symm

/-- The stabilizer over the actual fixed field has the size of the genuine intersection. -/
theorem card_stabilizer_fixedField (P : Ideal (𝓞 M)) :
    Nat.card (MulAction.stabilizer Gal(M/↥(fixedField H)) P) =
      Nat.card (MulAction.stabilizer Gal(M/ℚ) P ⊓ H : Subgroup Gal(M/ℚ)) :=
  card_fixedField_subgroup_eq_card_inf M H (comap_stabilizer_fixedField M H P)

/-- The inertia over the actual fixed field has the size of the genuine intersection. -/
theorem card_inertia_fixedField (P : Ideal (𝓞 M)) :
    Nat.card (P.inertia Gal(M/↥(fixedField H))) =
      Nat.card (P.inertia Gal(M/ℚ) ⊓ H : Subgroup Gal(M/ℚ)) :=
  card_fixedField_subgroup_eq_card_inf M H (comap_inertia_fixedField M H P)

variable (P : Ideal (𝓞 M)) [P.IsPrime]

/-- The actual global ramification index over a fixed field is the inertia-intersection order. -/
theorem ramificationIdx_fixedField_eq_card_inf :
    P.ramificationIdx (𝓞 ↥(fixedField H)) =
      Nat.card (P.inertia Gal(M/ℚ) ⊓ H : Subgroup Gal(M/ℚ)) := by
  let E := fixedField H
  let : IsGalois E M := IsGalois.of_fixed_field M H
  let : Module.Finite (𝓞 E) (𝓞 M) := Module.Finite.right ℤ (𝓞 E) (𝓞 M)
  rw [← card_inertia_fixedField M H P,
    Ideal.card_inertia_eq_ramificationIdxIn (P.under (𝓞 E)) P,
    Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 E)) P Gal(M/E)]

/-- The actual ramification/residue-degree product over a fixed field is the decomposition-
intersection order. No completion or local degree comparison is assumed. -/
theorem ramificationIdx_mul_inertiaDeg_fixedField_eq_card_inf :
    P.ramificationIdx (𝓞 ↥(fixedField H)) * P.inertiaDeg (𝓞 ↥(fixedField H)) =
      Nat.card (MulAction.stabilizer Gal(M/ℚ) P ⊓ H : Subgroup Gal(M/ℚ)) := by
  let E := fixedField H
  let : IsGalois E M := IsGalois.of_fixed_field M H
  let : Module.Finite (𝓞 E) (𝓞 M) := Module.Finite.right ℤ (𝓞 E) (𝓞 M)
  rw [← card_stabilizer_fixedField M H P, Ideal.card_stabilizer_eq (P.under (𝓞 E)) P,
    Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 E)) P Gal(M/E),
    Ideal.inertiaDegIn_eq_inertiaDeg (P.under (𝓞 E)) P Gal(M/E)]

end GlobalDifferentTransport
