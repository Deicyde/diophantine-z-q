import ZInQKernel.Contrib.DifferentBound.Generator
import ZInQKernel.Contrib.DifferentBound.Local
import ZInQKernel.Contrib.DifferentBound.Tower
import ZInQKernel.HDecomp.Conductor.I6Base

/-!
# Serre's general finite-complete-DVR bound

The unramified intermediate ring is constructed, not assumed. Its actual
residue-surjective inclusion supplies a generating uniformizer; the genuine
degree comparison and derivative estimate then give the bound. Transitivity of
the different and ramification index returns the bound to the original rings.

`localDifferentBound` is a closed proof of the baseline LOCAL proposition
`PkgI6.DifferentBound`. It is not a closed proof of the global target T21.
-/

namespace ZInQ.Contrib.DifferentBound

open IsLocalRing
open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- A finite extension of DVRs is the actual integral closure in its upper fraction field.
The proof uses integral transitivity upwards and normality of the upper DVR. -/
theorem dvr_isIntegralClosure_fractionRing
    (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [Module.Finite R S] [Module.IsTorsionFree R S] :
    IsIntegralClosure S R (FractionRing S) := by
  refine ⟨IsFractionRing.injective S _, ?_⟩
  intro x
  constructor
  · intro hx
    have hxS : IsIntegral S x := hx.tower_top
    exact IsIntegrallyClosed.isIntegral_iff.mp hxS
  · rintro ⟨y, rfl⟩
    exact IsIntegral.algebraMap (IsIntegral.of_finite R y)

/-- The extension of the actual fraction fields of a finite DVR algebra is finite dimensional. -/
theorem dvr_fractionRing_finite
    (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [Module.Finite R S] [Module.IsTorsionFree R S] :
    FiniteDimensional (FractionRing R) (FractionRing S) := by
  have := dvr_isIntegralClosure_fractionRing R S
  have : IsLocalization (Algebra.algebraMapSubmonoid S R⁰) (FractionRing S) :=
    IsIntegralClosure.isLocalization R (FractionRing R) (FractionRing S) S
  exact Module.Finite.of_isLocalization R S R⁰

/-- Serre's ideal-form bound from a supplied actual unramified intermediate DVR.
Neither completeness nor perfectness is assumed for this inequality: those properties are
used only when constructing such a factor. No bound is stored in the factor record. -/
theorem differentIdeal_bound_of_factor
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    (F : UnramifiedDVRFactor A B) :
    differentIdeal A B ∣ maximalIdeal B ^ ((maximalIdeal B).ramificationIdx A - 1) *
      Ideal.span {((maximalIdeal B).ramificationIdx A : B)} := by
  let U := F.carrier
  have : IsDiscreteValuationRing U := F.isDvr
  have : Module.Finite A U := F.finiteBase
  have : FaithfulSMul A U := F.faithfulBase
  have : Module.Finite U B := F.finiteTop
  have : Algebra.Etale A U := F.etale
  have : Module.IsTorsionFree A U := inferInstance
  have : Module.IsTorsionFree U B := inferInstance
  have : (maximalIdeal B).LiesOver (maximalIdeal U) := inferInstance
  have : Algebra.IsUnramifiedAt A (maximalIdeal U) := F.isUnramifiedAt
  -- Use the canonical composite U → B → Frac(B), rather than the alternate
  -- subalgebra algebra instance on the fraction field. This fixes the scalar
  -- tower to the same maps as the integral-closure/fraction-field APIs.
  let : Algebra U (FractionRing B) := OreLocalization.instAlgebra
  have : IsIntegralClosure B U (FractionRing B) := dvr_isIntegralClosure_fractionRing U B
  have : FiniteDimensional (FractionRing U) (FractionRing B) := dvr_fractionRing_finite U B
  have : Algebra.IsSeparable (FractionRing U) (FractionRing B) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      (FractionRing A) (FractionRing U) (FractionRing B)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hgen : Algebra.adjoin U {π} = ⊤ :=
    adjoin_eq_top_of_residue_surjective_uniformizer F.residue_surjective_algebraMap hπ
  have htot : (maximalIdeal B).ramificationIdx U =
      Module.finrank (FractionRing U) (FractionRing B) :=
    dvr_ramificationIdx_eq_fractionField_finrank_of_surjective_residue
      U B (FractionRing U) (FractionRing B) F.residue_surjective_algebraMap
  exact differentIdeal_bound_of_unramified_tower A U B hπ hgen htot

/-- The same noncomplete inequality for a supplied genuine unramified DVR tower whose top
residue map is surjective. This interface needs neither a packaged factor nor completeness. -/
theorem differentIdeal_bound_of_residue_surjective_unramified_tower
    (A U B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A U] [Algebra U B] [Algebra A B] [IsScalarTower A U B]
    [Module.Finite A U] [Module.Finite U B] [Module.Finite A B]
    [Module.IsTorsionFree A U] [Module.IsTorsionFree U B] [Module.IsTorsionFree A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [Algebra.IsUnramifiedAt A (maximalIdeal U)]
    (hres : Function.Surjective ((residue B).comp (algebraMap U B))) :
    differentIdeal A B ∣ maximalIdeal B ^ ((maximalIdeal B).ramificationIdx A - 1) *
      Ideal.span {((maximalIdeal B).ramificationIdx A : B)} := by
  have : (maximalIdeal B).LiesOver (maximalIdeal U) := inferInstance
  let : Algebra U (FractionRing B) := OreLocalization.instAlgebra
  have : IsIntegralClosure B U (FractionRing B) := dvr_isIntegralClosure_fractionRing U B
  have : FiniteDimensional (FractionRing U) (FractionRing B) := dvr_fractionRing_finite U B
  have : Algebra.IsSeparable (FractionRing U) (FractionRing B) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      (FractionRing A) (FractionRing U) (FractionRing B)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hgen : Algebra.adjoin U {π} = ⊤ :=
    adjoin_eq_top_of_residue_surjective_uniformizer hres hπ
  have htot : (maximalIdeal B).ramificationIdx U =
      Module.finrank (FractionRing U) (FractionRing B) :=
    dvr_ramificationIdx_eq_fractionField_finrank_of_surjective_residue
      U B (FractionRing U) (FractionRing B) hres
  exact differentIdeal_bound_of_unramified_tower A U B hπ hgen htot

/-- Completeness and perfectness are used only to construct the genuine unramified factor;
the inequality then follows from `differentIdeal_bound_of_factor`. -/
theorem differentIdeal_bound_completeDVR
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)] :
    differentIdeal A B ∣ maximalIdeal B ^ ((maximalIdeal B).ramificationIdx A - 1) *
      Ideal.span {((maximalIdeal B).ramificationIdx A : B)} :=
  differentIdeal_bound_of_factor A B (Classical.choice
    (UnramifiedFactor.nonempty_of_perfect (A := A) (B := B)))

/-- The baseline LOCAL leaf is closed without an assumed Serre or Hilbert bound.
Global target T21 additionally requires its exact global-to-completion comparison. -/
theorem localDifferentBound : PkgI6.DifferentBound := by
  unfold PkgI6.DifferentBound
  intros
  apply differentIdeal_bound_completeDVR

#print PkgI6.DifferentBound
#check @differentIdeal_bound_of_factor
#check @differentIdeal_bound_of_residue_surjective_unramified_tower
#check @differentIdeal_bound_completeDVR
#check @localDifferentBound
#print axioms differentIdeal_bound_of_factor
#print axioms differentIdeal_bound_of_residue_surjective_unramified_tower
#print axioms differentIdeal_bound_completeDVR
#print axioms localDifferentBound

end ZInQ.Contrib.DifferentBound
