import FrobeniusGroupPointsSecond
import FrobLift.ResidueFrobeniusV001

/-!
# The finite fixed group for the actual valuation-residue Frobenius

The residue base map is the genuine quotient map through the integral
closure residue field. The number-field Frobenius lift supplies the actual
decomposition element and its residue power law. Its positive powers have
finitely many fixed geometric points on the actual finite-type special
scheme, by fixed-field polynomial finiteness and actual Spec descent.
No modeled operator action, fixed-point bound, or Frobenius hypothesis is
introduced in the existence theorem.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace SemistableGeometry.ActualResidueFrobenius

open SemistableGeometry.FrobeniusFixed
attribute [local instance] FrobLift.primeQ_liesOver

variable {K : Type} [Field K] [NumberField K]
variable {O : ValuationSubring K} [IsDiscreteValuationRing O]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
variable {w : ValuationSubring Ω}

/-- The actual map from the base residue field to the valuation residue field. -/
def residueBase (hw : w.comap (algebraMap K Ω) = O) :
    IsLocalRing.ResidueField O →+* IsLocalRing.ResidueField w :=
  by
    have h : IsLocalRing.maximalIdeal O ≤ (FrobLift.primeQ hw).comap
        (algebraMap O (integralClosure O Ω)) := by
      rw [← Ideal.under_def, Ideal.over_def (FrobLift.primeQ hw) (IsLocalRing.maximalIdeal O)]
    exact (FrobLift.resB hw).comp
      (Ideal.quotientMap (FrobLift.primeQ hw) (algebraMap O (integralClosure O Ω)) h)

/-- The residue base map is compatible with the original integral base map. -/
theorem residueBase_comp_residue (hw : w.comap (algebraMap K Ω) = O) :
    (residueBase hw).comp (IsLocalRing.residue O) =
      (IsLocalRing.residue w).comp (FrobLift.incO hw) := by
  ext a
  rfl

/-- The algebra structure is induced by that actual residue base map. -/
def residueAlgebra (hw : w.comap (algebraMap K Ω) = O) :
    Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) :=
  (residueBase hw).toAlgebra

/-- The actual native residue Frobenius, now with its proved base-field fixing property. -/
def residueFrobeniusAlg (hw : w.comap (algebraMap K Ω) = O)
    (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K)
    (hcong : ∀ x ∈ w, w.valuation (σ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1) :
    letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) := residueAlgebra hw
    IsLocalRing.ResidueField w ≃ₐ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField w := by
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) := residueAlgebra hw
  letI : Finite (IsLocalRing.ResidueField O) := FrobLift.finite_residueField O
  exact ofRingFrobenius
    (MulSemiringAction.toRingAut (w.decompositionSubgroup K) (IsLocalRing.ResidueField w) ⟨σ, hD⟩)
    (FrobLift.residue_toRingAut_apply hD hcong)

/-- Its power is exactly the native residue action of the original decomposition-element power. -/
theorem residueFrobeniusAlg_pow_apply (hw : w.comap (algebraMap K Ω) = O)
    (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K)
    (hcong : ∀ x ∈ w, w.valuation (σ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1)
    (r : ℕ) (a : IsLocalRing.ResidueField w) :
    letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) := residueAlgebra hw
    (residueFrobeniusAlg hw σ hD hcong ^ r) a =
      MulSemiringAction.toRingAut (w.decompositionSubgroup K) (IsLocalRing.ResidueField w)
        ((⟨σ, hD⟩ : w.decompositionSubgroup K) ^ r) a := by
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) := residueAlgebra hw
  letI : Finite (IsLocalRing.ResidueField O) := FrobLift.finite_residueField O
  have ha : (residueFrobeniusAlg hw σ hD hcong ^ r) a =
      a ^ (Nat.card (IsLocalRing.ResidueField O) ^ r) :=
    power_apply (residueFrobeniusAlg hw σ hD hcong)
      (Nat.card (IsLocalRing.ResidueField O))
      (FrobLift.residue_toRingAut_apply hD hcong) r a
  exact ha.trans (FrobLift.residue_toRingAut_pow_apply hD hcong r a).symm

/-- The actual lift, not a supplied Frobenius operator, gives the finite fixed special-point group. -/
theorem exists_frobenius_finite_fixed_special_group
    (hw : w.comap (algebraMap K Ω) = O)
    (G : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField O)))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [CompactSpace G.left] :
    ∃ (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K)
      (hcong : ∀ x ∈ w, w.valuation (σ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1),
      ∀ (r : ℕ), 0 < r →
        letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) := residueAlgebra hw
        Finite (fixedPointSubgroup (residueFrobeniusAlg hw σ hD hcong) r G) := by
  obtain ⟨σ, hD, hcong⟩ := FrobLift.exists_frobenius_lift hw
  refine ⟨σ, hD, hcong, ?_⟩
  intro r hr
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) := residueAlgebra hw
  exact finite_fixedPointSubgroup (residueFrobeniusAlg hw σ hD hcong)
    (Nat.card (IsLocalRing.ResidueField O)) (FrobLift.two_le_card_residueField O)
    (FrobLift.residue_toRingAut_apply hD hcong) r hr G

end SemistableGeometry.ActualResidueFrobenius
