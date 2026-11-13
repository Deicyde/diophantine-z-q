import ZInQKernel.HDecomp.Descent.B2Glue
import Mathlib.FieldTheory.Galois.Abelian

/-!
# Actual absolute-Galois quotients used by the local square-root criterion

The kernel of a locally constant character is open in the Krull topology. Infinite Galois
correspondence therefore gives a finite abelian fixed field. Character descent uses the
surjective normal restriction map, and inflation is locally constant because its kernel
contains the open fixing subgroup of the finite field.
-/

namespace ZInQ.Contrib.LocalSquareRoot

open scoped Pointwise

/-- A locally constant complex character cuts out an actual finite abelian extension. -/
theorem exists_finite_abelian_kernel (F : Type) [Field F] [PerfectField F]
    (χ : Field.absoluteGaloisGroup F →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ∃ M : IntermediateField F (AlgebraicClosure F),
      FiniteDimensional F M ∧ IsAbelianGalois F M ∧ M.fixingSubgroup ≤ χ.ker := by
  let φ : Gal(AlgebraicClosure F/F) →* ℂˣ := χ
  have hopen : IsOpen (φ.ker : Set Gal(AlgebraicClosure F/F)) :=
    (IsLocallyConstant.iff_isOpen_fiber.mp hχ) 1
  let H : ClosedSubgroup Gal(AlgebraicClosure F/F) :=
    ⟨φ.ker, OpenSubgroup.isClosed ⟨φ.ker, hopen⟩⟩
  let M : IntermediateField F (AlgebraicClosure F) := IntermediateField.fixedField H.toSubgroup
  have hfix : M.fixingSubgroup = φ.ker := InfiniteGalois.fixingSubgroup_fixedField H
  haveI : FiniteDimensional F M := (InfiniteGalois.isOpen_iff_finite M).mp (by
    rw [hfix]
    exact hopen)
  haveI : IsGalois F M := (InfiniteGalois.normal_iff_isGalois M).mp (by
    rw [hfix]
    infer_instance)
  haveI : H.Normal := inferInstanceAs φ.ker.Normal
  let e : Gal(M/F) ≃* φ.range :=
    (InfiniteGalois.normalAutEquivQuotient H).symm.trans
      (QuotientGroup.quotientKerEquivRange φ)
  haveI : IsMulCommutative Gal(M/F) := .of_comm fun a b => e.injective (by
    rw [map_mul, map_mul, mul_comm])
  haveI : IsAbelianGalois F M := {}
  exact ⟨M, inferInstance, inferInstance, by
    rw [hfix]
    exact fun _ h => h⟩

section Descent

variable (F : Type) [Field F] {U : Type*} [Group U]

/-- Descend a character through actual normal restriction, using its kernel inclusion. -/
noncomputable def descendCharacter
    (M : IntermediateField F (AlgebraicClosure F)) [Normal F M]
    (χ : Field.absoluteGaloisGroup F →* U) (hχ : M.fixingSubgroup ≤ χ.ker) :
    Gal(M/F) →* U :=
  (AlgEquiv.restrictNormalHom M).liftOfSurjective
    (AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure F))
    ⟨χ, by rw [M.restrictNormalHom_ker]; exact hχ⟩

/-- Descent consumes exactly the original character, not just an isomorphic quotient. -/
theorem descendCharacter_apply
    (M : IntermediateField F (AlgebraicClosure F)) [Normal F M]
    (χ : Field.absoluteGaloisGroup F →* U) (hχ : M.fixingSubgroup ≤ χ.ker)
    (g : Field.absoluteGaloisGroup F) :
    descendCharacter F M χ hχ (g.restrictNormal M) = χ g := by
  unfold descendCharacter
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g

/-- Inflation from a finite normal field is locally constant for the actual Krull topology. -/
theorem inflatedCharacter_isLocallyConstant
    (M : IntermediateField F (AlgebraicClosure F)) [Normal F M] [FiniteDimensional F M]
    (χ : Gal(M/F) →* U) :
    IsLocallyConstant (χ.comp (AlgEquiv.restrictNormalHom M) :
      Field.absoluteGaloisGroup F →* U) := by
  change IsLocallyConstant (fun g : Gal(AlgebraicClosure F/F) => χ (g.restrictNormal M))
  apply GlueDescent.B2Q.isLocallyConstant_of_openSubgroup M.fixingSubgroup
    M.fixingSubgroup_isOpen
  intro g k hk
  have hfix : AlgEquiv.restrictNormalHom M k = 1 := by
    have : k ∈ (AlgEquiv.restrictNormalHom M).ker := by
      rw [M.restrictNormalHom_ker]
      exact hk
    exact this
  change χ (AlgEquiv.restrictNormalHom M (g * k)) = χ (AlgEquiv.restrictNormalHom M g)
  simp only [map_mul, hfix, map_one, mul_one]

end Descent

/-- Normal restriction is transitive through the actual scalar-tower maps.
The proof never unfolds a cyclotomic generator or the chosen normal-field equivalence. -/
theorem restrictNormal_trans
    {F K L Ω : Type} [Field F] [Field K] [Field L] [Field Ω]
    [Algebra F K] [Algebra F L] [Algebra F Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower F K L] [IsScalarTower F K Ω] [IsScalarTower F L Ω]
    [IsScalarTower K L Ω] [Normal F K] [Normal F L]
    (g : Gal(Ω/F)) :
    (g.restrictNormal L).restrictNormal K = g.restrictNormal K := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap K Ω).injective
  calc
    algebraMap K Ω ((g.restrictNormal L).restrictNormal K x) =
        algebraMap L Ω (algebraMap K L ((g.restrictNormal L).restrictNormal K x)) :=
      IsScalarTower.algebraMap_apply K L Ω _
    _ = algebraMap L Ω (g.restrictNormal L (algebraMap K L x)) :=
      congrArg (algebraMap L Ω) (AlgEquiv.restrictNormal_commutes (g.restrictNormal L) K x)
    _ = g (algebraMap L Ω (algebraMap K L x)) :=
      AlgEquiv.restrictNormal_commutes g L _
    _ = g (algebraMap K Ω x) := by rw [IsScalarTower.algebraMap_apply K L Ω]
    _ = algebraMap K Ω (g.restrictNormal K x) :=
      (AlgEquiv.restrictNormal_commutes g K x).symm

end ZInQ.Contrib.LocalSquareRoot
