import ZInQKernel.Contrib.HilbertDifferent.LocalizationModel
import ZInQKernel.Contrib.HilbertDifferent.PrimeLocalization

/-!
# Decomposition-group automorphisms of the actual prime localization

The equivalence is the composition of Mathlib's subgroup/fixed-field Galois
correspondence and `galRestrict` for the true localized integral closure. Its
inverse is restriction/extension through the actual fraction fields; neither
surjectivity nor the target group is supplied as a premise or inferred from a
cardinality shortcut. Equivariance is checked on the original integer-ring
inclusion into the localization and its original field.

All nonnegative lower indices and all prime powers are compared, using the
actual quotient isomorphisms for prime localization. No completed integer ring
or completed-different equality enters this argument.
-/

noncomputable section

open NumberField
open scoped Pointwise HilbertDifferentLocalization

namespace ZInQ.Contrib.HilbertDifferent

open LocalizationModel

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
  (P : Ideal (𝓞 L)) [P.IsPrime]

/-- The Galois correspondence on the actual supplied fixed field, with that field's
canonical scalar structure made explicit in the result type. -/
def localizationFieldEquiv :
    MulAction.stabilizer Gal(L/ℚ) P ≃* Gal(L/↥(decompField L P)) :=
  IntermediateField.subgroupEquivAlgEquiv (MulAction.stabilizer Gal(L/ℚ) P)

/-- Rebundling a decomposition automorphism does not change its value in the original field. -/
theorem localizationFieldEquiv_apply (σ : MulAction.stabilizer Gal(L/ℚ) P) (x : L) :
    localizationFieldEquiv L P σ x = (σ : Gal(L/ℚ)) x := rfl

/-- The actual decomposition group is the group of automorphisms of the finite localized
integer-ring extension over the localized decomposition fixed field. -/
def localizationDecompositionEquiv :
    MulAction.stabilizer Gal(L/ℚ) P ≃*
      (topRing L P ≃ₐ[baseRing L P] topRing L P) :=
  (localizationFieldEquiv L P).trans
    (galRestrict (baseRing L P) (decompField L P) L (topRing L P))

/-- On the actual original integers, the localized automorphism is precisely the image of
the same global decomposition automorphism. This fixes the action and map orientations. -/
theorem localizationDecompositionEquiv_algebraMap
    (σ : MulAction.stabilizer Gal(L/ℚ) P) (x : 𝓞 L) :
    algebraMap (𝓞 L) (topRing L P) (σ • x) =
      localizationDecompositionEquiv L P σ (algebraMap (𝓞 L) (topRing L P) x) := by
  apply IsFractionRing.injective (topRing L P) L
  calc
    algebraMap (topRing L P) L (algebraMap (𝓞 L) (topRing L P) (σ • x)) =
        algebraMap (𝓞 L) L (σ • x) :=
      (IsScalarTower.algebraMap_apply (𝓞 L) (topRing L P) L (σ • x)).symm
    _ = (σ : Gal(L/ℚ)) (algebraMap (𝓞 L) L x) := integralClosure.coe_smul σ x
    _ = localizationFieldEquiv L P σ (algebraMap (𝓞 L) L x) :=
      (localizationFieldEquiv_apply L P σ _).symm
    _ = localizationFieldEquiv L P σ
        (algebraMap (topRing L P) L (algebraMap (𝓞 L) (topRing L P) x)) :=
      congrArg (localizationFieldEquiv L P σ)
        (IsScalarTower.algebraMap_apply (𝓞 L) (topRing L P) L x)
    _ = algebraMap (topRing L P) L
        (localizationDecompositionEquiv L P σ (algebraMap (𝓞 L) (topRing L P) x)) :=
      (algebraMap_galRestrict_apply (baseRing L P) (K := ↥(decompField L P))
        (L := L) (B := topRing L P)
        (localizationFieldEquiv L P σ) (algebraMap (𝓞 L) (topRing L P) x)).symm

/-- Inside the decomposition group, the actual global lower group is the pullback of the
localized lower group along the constructed equivalence, for every natural index. -/
theorem ramGroup_localization_comap (hP : P ≠ ⊥) (i : ℕ) :
    (GlueConductor.ramGroup L P i).subgroupOf (MulAction.stabilizer Gal(L/ℚ) P) =
      ((IsLocalRing.maximalIdeal (topRing L P) ^ (i + 1)).inertia
        (topRing L P ≃ₐ[baseRing L P] topRing L P)).comap
          (localizationDecompositionEquiv L P).toMonoidHom := by
  let : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hP
  rw [powerInertia_subgroupOf]
  exact powerInertia_eq_comap_of_equivariant_dense P
    (IsLocalRing.maximalIdeal (topRing L P)) (localizationDecompositionEquiv L P).toMonoidHom
    (algebraMap (𝓞 L) (topRing L P))
    (localizationDecompositionEquiv_algebraMap L P)
    (primeLocalization_comap_maximalIdeal_pow P)
    (fun σ n y hy ↦ algAut_mem_maximalIdeal_pow (localizationDecompositionEquiv L P σ) n hy)
    (primeLocalization_surjective_mod_pow P) i

/-- Exact global/localized lower-group cardinality comparison at every nonnegative index.
No ramification index, residue degree or ambient field-degree factor is inserted. -/
theorem ramCard_eq_card_localization (hP : P ≠ ⊥) (i : ℕ) :
    GlueConductor.ramCard L P i =
      Nat.card ((IsLocalRing.maximalIdeal (topRing L P) ^ (i + 1)).inertia
        (topRing L P ≃ₐ[baseRing L P] topRing L P)) := by
  let : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hP
  rw [ramCard_eq_card_powerInertia_stabilizer]
  exact card_powerInertia_eq_of_equivariant_dense P
    (IsLocalRing.maximalIdeal (topRing L P)) (localizationDecompositionEquiv L P)
    (algebraMap (𝓞 L) (topRing L P))
    (localizationDecompositionEquiv_algebraMap L P)
    (primeLocalization_comap_maximalIdeal_pow P)
    (fun σ n y hy ↦ algAut_mem_maximalIdeal_pow (localizationDecompositionEquiv L P σ) n hy)
    (primeLocalization_surjective_mod_pow P) i

/-- The original global group is trivial exactly when the matching localized group is
trivial. This includes an empty-range Hilbert witness and the trivial ambient-group case. -/
theorem ramGroup_eq_bot_iff_localization (hP : P ≠ ⊥) (i : ℕ) :
    GlueConductor.ramGroup L P i = ⊥ ↔
      (IsLocalRing.maximalIdeal (topRing L P) ^ (i + 1)).inertia
        (topRing L P ≃ₐ[baseRing L P] topRing L P) = ⊥ := by
  rw [← Subgroup.card_eq_one, ← Subgroup.card_eq_one]
  change GlueConductor.ramCard L P i = 1 ↔ _
  rw [ramCard_eq_card_localization L P hP i]

end ZInQ.Contrib.HilbertDifferent
