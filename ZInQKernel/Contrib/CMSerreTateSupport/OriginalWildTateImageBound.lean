import ZInQKernel.Contrib.CMSerreTateSupport.FiniteProjectionTateBasisCoherent
import ZInQKernel.Contrib.CMSerreTateSupport.OriginalDivisionMatrixScalarImage
import ZInQKernel.Contrib.CMSerreTateSupport.NumberFieldResiduePrimeAlgebraic
import ZInQKernel.Contrib.CloudB3W16Torsion.NativeBridges
import ZInQKernel.Contrib.AbVarBC.Points

/-!
# Finiteness of the original wild-inertia Tate image

Prime-to-characteristic multiplication on the actual abelian variety is
finite. This gives finite original first torsion. The basis of the whole
original Tate module is then constructed from its actual first projection
image and compatible shifts. Its rank is not supplied, and no claim that
it equals twice the dimension is needed here.

The original Galois action has residue-prime finite-level images. The
actual congruence kernel is pro-ell; the two primes are distinct because
ell is a unit at the original valuation ring. The whole integral image
injects into the finite residual image, so the original rational Tate
image is finite too. No semistability or identity conclusion is used.
-/

noncomputable section
set_option autoImplicit false

namespace OriginalWildTateImage

open CategoryTheory AlgebraicGeometry MonObj Matrix
open NativeTateCongruence ActualFiniteLevel

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

/-- Actual original torsion finiteness, with no cardinality or finite-action input. -/
theorem original_torsion_finite [IsAlgClosed Ω] (A : PkgI3.AbVar K) (m : ℕ) (hm : (m : Ω) ≠ 0) :
    Finite (torsionSubgroup A Ω m) := by
  let B := A.baseChange Ω
  let E := ZInQ.Contrib.AbVarBC.bcPt (L := Ω) A Ω
  let e : {x : B.Pt Ω // x ^ m = 1} ≃ {x : A.Pt Ω // x ^ m = 1} :=
    { toFun := fun x => ⟨E x.1, by rw [← map_pow, x.2, map_one]⟩
      invFun := fun x => ⟨E.symm x.1, by rw [← map_pow, x.2, map_one]⟩
      left_inv := fun x => Subtype.ext (E.symm_apply_apply x.1)
      right_inv := fun x => Subtype.ext (E.apply_symm_apply x.1) }
  haveI : Finite {x : B.Pt Ω // x ^ m = 1} :=
    ZInQ.Contrib.CloudB3W16Torsion.finite_torsion (ObjBridge.toGrp B) m hm
  exact Finite.of_equiv _ e

/-- The needed entire original Tate basis is derived from finite actual
first torsion and the literal compatible-sequence object. -/
theorem original_tate_basis [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (ell : ℕ) [Fact ell.Prime] :
    ∃ r : ℕ, Nonempty (PkgI3.Tate.T ell (Additive (A.Pt Ω)) ≃ₗ[ℤ_[ell]] (Fin r → ℤ_[ell])) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI : Finite (torsionSubgroup A Ω ell) :=
    original_torsion_finite A ell (Nat.cast_ne_zero.mpr (Fact.out : ell.Prime).ne_zero)
  let e : AddSubgroup.torsionBy (Additive (A.Pt Ω)) (ell : ℤ) ≃ torsionSubgroup A Ω ell :=
    { toFun := fun x => ⟨Additive.toMul x.1,
        congrArg Additive.toMul (AddSubgroup.torsionBy.nsmul_iff.mp x.2)⟩
      invFun := fun x => ⟨Additive.ofMul x.1,
        AddSubgroup.torsionBy.nsmul_iff.mpr (congrArg Additive.ofMul x.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Finite (AddSubgroup.torsionBy (Additive (A.Pt Ω)) (ell : ℤ)) := Finite.of_equiv _ e.symm
  exact FiniteProjectionTate.tate_equiv_of_finite_first_torsion

/-- Finiteness of the entire original integral action of literal wild
inertia, with no finite-image, rank, basis or pro-p premise from a caller. -/
theorem original_integral_wild_image_finite [NumberField K] [IsAlgClosure K Ω]
    (O : ValuationSubring K) [IsDiscreteValuationRing O] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K)
    (ell : ℕ) [Fact ell.Prime] (hu : IsUnit (ell : O)) :
    (Set.range fun sigma : WildFiniteGroup.strictDisplacementGroup (K := K) w =>
      originalTateRep A ell sigma.1).Finite := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  obtain ⟨r, ⟨E⟩⟩ := original_tate_basis (Ω := Ω) A ell
  let b : Module.Basis (Fin r) ℤ_[ell] (PkgI3.Tate.T ell (Additive (A.Pt Ω))) :=
    (Pi.basisFun ℤ_[ell] (Fin r)).map E.symm
  haveI : ∀ n : ℕ, Finite (torsionSubgroup A Ω (ell ^ (n + 1))) := fun n =>
    original_torsion_finite A (ell ^ (n + 1)) (by
      rw [Nat.cast_pow]
      exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : ell.Prime).ne_zero))
  obtain ⟨p, hp, hchar⟩ := ValuationResidueCharacteristic.numberField_residue_prime O
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (IsLocalRing.ResidueField O) p := hchar
  haveI : CharP (IsLocalRing.ResidueField (w.comap (algebraMap K Ω))) p := by rw [hw]; infer_instance
  haveI : CharP (IsLocalRing.ResidueField w) p :=
    (ValuationResidueCharacteristic.residue_charP_iff w (algebraMap K Ω) p).mp inferInstance
  have hne := ValuationResidueCharacteristic.prime_ne_of_isUnit O p ell hu
  have hfin := wild_matrix_image_finite A ell b w p hne
  let F : GL (Fin r) ℤ_[ell] → (PkgI3.Tate.T ell (Additive (A.Pt Ω)) →ₗ[ℤ_[ell]]
      PkgI3.Tate.T ell (Additive (A.Pt Ω))) := fun g => (LinearMap.toMatrixAlgEquiv b).symm g.val
  have he : (fun sigma : WildFiniteGroup.strictDisplacementGroup (K := K) w => originalTateRep A ell sigma.1) =
      F ∘ wildIntegralMatrix A ell b w := by
    funext sigma
    simp [F, wildIntegralMatrix, originalTateMatrix, Representation.asGroupHom_apply]
  rw [he]
  rw [Set.range_comp]
  exact hfin.image F

/-- Finiteness on the original rational Tate module `A.V ell`, acted on
by the original `A.galRep`; not an arbitrary supplied representation. -/
theorem original_rational_wild_image_finite [NumberField K]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O) (A : PkgI3.AbVar K)
    (ell : ℕ) [Fact ell.Prime] (hu : IsUnit (ell : O)) :
    (Set.range fun sigma : WildFiniteGroup.strictDisplacementGroup (K := K) w => A.galRep ell sigma.1).Finite := by
  have h := original_integral_wild_image_finite O w hw A ell hu
  let F : (A.T ell →ₗ[ℤ_[ell]] A.T ell) → (A.V ell →ₗ[ℚ_[ell]] A.V ell) :=
    fun f => f.baseChange ℚ_[ell]
  have he : (fun sigma : WildFiniteGroup.strictDisplacementGroup (K := K) w => A.galRep ell sigma.1) =
      F ∘ (fun sigma : WildFiniteGroup.strictDisplacementGroup (K := K) w => originalTateRep A ell sigma.1) := rfl
  rw [he]
  rw [Set.range_comp]
  exact h.image F

#check original_torsion_finite
#print axioms original_torsion_finite
#check original_tate_basis
#print axioms original_tate_basis
#check original_integral_wild_image_finite
#print axioms original_integral_wild_image_finite
#check original_rational_wild_image_finite
#print axioms original_rational_wild_image_finite

end OriginalWildTateImage
