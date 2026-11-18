import ActualNumberFieldDivisionV001
import ActualNumberFieldQuotientV001
import OriginalWildTateImageBound
import OriginalTateLatticeContinuity
import TameGeneratorClosedV001
import FrobLift.CorollariesV003
import FrobLift.FinitePlaceV002
import HenselDivision.ValuationTorsionV001

open CategoryTheory AlgebraicGeometry MonObj

#check @ActualNumberFieldDivision.genuine_division_factor
#print axioms ActualNumberFieldDivision.genuine_division_factor
#check @ActualNumberFieldDivision.actual_wild_finite_restriction
#print axioms ActualNumberFieldDivision.actual_wild_finite_restriction
#check @ActualNumberFieldDivision.uniform_torsion_period
#print axioms ActualNumberFieldDivision.uniform_torsion_period
#check @ActualNumberFieldQuotient.actualQuotient
#print axioms ActualNumberFieldQuotient.actualQuotient
#check @OriginalWildTateImage.original_tate_basis
#print axioms OriginalWildTateImage.original_tate_basis
#check @OriginalWildTateImage.original_integral_wild_image_finite
#print axioms OriginalWildTateImage.original_integral_wild_image_finite
#check @OriginalWildTateImage.original_rational_wild_image_finite
#print axioms OriginalWildTateImage.original_rational_wild_image_finite
#check @ActualTameInertia.leaf_tame_generator
#print axioms ActualTameInertia.leaf_tame_generator
#check @FrobLift.exists_frobenius_lift
#print axioms FrobLift.exists_frobenius_lift
#check @HenselDivision.SmoothCommMulEtale.multiplication_etale_of_smooth_comm
#print axioms HenselDivision.SmoothCommMulEtale.multiplication_etale_of_smooth_comm
#check @HenselDivision.henselianLocalRing_of_isAlgClosed
#print axioms HenselDivision.henselianLocalRing_of_isAlgClosed
#check @HenselDivision.isAlgClosed_residueField
#print axioms HenselDivision.isAlgClosed_residueField

example (K : Type) [Field K] [NumberField K] (O : ValuationSubring K)
    [IsDiscreteValuationRing O] (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (hu : IsUnit (ℓ : O)) :
    (Set.range fun σ : WildFiniteGroup.strictDisplacementGroup (K := K) w =>
      A.galRep ℓ σ.1).Finite :=
  OriginalWildTateImage.original_rational_wild_image_finite O w hw A ℓ hu

example {O : Type} [CommRing O] (G : Grp (Over (Spec (.of O))))
    [Smooth G.X.hom] [IsCommMonObj G.X] (m : ℕ) (hm : IsUnit (m : O)) :
    Etale ((𝟙 G.X ^ m).left) :=
  HenselDivision.SmoothCommMulEtale.multiplication_etale_of_smooth_comm G m hm
