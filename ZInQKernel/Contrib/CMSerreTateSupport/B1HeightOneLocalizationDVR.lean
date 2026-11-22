/-
Copyright (c) 2026 H5 contributors. Apache-2.0.

# Height-one localizations of the original affine section ring

The stalks of the smooth field scheme give regularity of the original
affine section ring and its localization at the given prime. The prime's
height determines the local ring dimension.

The native cotangent criterion proves that a regular one-dimensional local
domain is a discrete valuation ring. All rings, affine opens, primes and
localization maps remain those originally given; no completion or additional
rank, characteristic or dimension assumption is used.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.LocalizedComapInterface
import ZInQKernel.Contrib.CMSerreTateSupport.I0SmoothFieldStalkRegular
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace H5OriginalDVR.Lane2.B1HeightOneLocalization

/-- The actual native regular-local/domain/dimension-one criterion. Finrank
of the cotangent is DERIVED from regularity, not supplied as an extra rank
or model premise. This helper applies to the SAME ring, not a completion. -/
theorem regularLocal_dimOne_isDVR
    (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (hDim : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  apply (IsLocalRing.finrank_CotangentSpace_eq_one_iff (R := R)).mp
  have hcot := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp
    (inferInstance : IsRegularLocalRing R)
  rw [hDim] at hcot
  exact_mod_cast hcot

/-- Exact original AV/affine/prime L3 type. All geometry/domain/local/regular
structures are produced from the original A, U and p; no new Fact input. -/
theorem height_one_localization_isDVR
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (U : A.X.left.affineOpens) (p : PrimeSpectrum Γ(A.X.left, U.1))
    (hp : p.asIdeal.height = 1) :
    ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
      IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) := by
  haveI : Smooth A.X.hom := PkgI2.IsAbelianVariety.smooth
  haveI : GeometricallyIntegral A.X.hom := PkgI2.IsAbelianVariety.geomIntegral
  haveI : IsLocallyNoetherian A.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian A.X.hom
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  have hU : IsAffineOpen U.1 := by
    change U.1 ∈ A.X.left.affineOpens
    exact U.2
  have hηU : hU.fromSpec p ∈ (U.1 : Set A.X.left) := by
    have hr : hU.fromSpec p ∈ Set.range hU.fromSpec := ⟨p, rfl⟩
    exact Eq.mp
      (congrArg (fun Z : Set A.X.left => hU.fromSpec p ∈ Z) hU.range_fromSpec) hr
  letI : Nonempty U.1 := ⟨⟨hU.fromSpec p, hηU⟩⟩
  letI : IsDomain Γ(A.X.left, U.1) := inferInstance
  letI : IsNoetherianRing Γ(A.X.left, U.1) :=
    IsLocallyNoetherian.component_noetherian U
  letI : IsRegularRing Γ(A.X.left, U.1) :=
    (TauCeti.AlgebraicGeometry.isRegularRing_iff_isRegularLocalRing_stalk hU).mpr
      (fun x _ => H5OriginalDVR.Lane5.I0Native.smoothFieldStalkRegular A.X.hom x)
  let L := Localization.AtPrime p.asIdeal
  letI : IsDomain L := inferInstance
  letI : IsRegularLocalRing L := inferInstance
  have hDim : ringKrullDim L = 1 := by
    simpa [hp] using (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal L)
  exact ⟨inferInstance, regularLocal_dimOne_isDVR L hDim⟩

/-- EXACT frozen consumer Prop, with no A1/UFD/localization/regularity Fact
or extra proof argument. Source-only until C6/default/runtime admission. -/
theorem heightOneLocalizationDVR :
    ZInQ.Contrib.CloudR2NOS.Step2B1.HeightOneLocalizationDVR.{u} := by
  intro K _ _ A _ U p hp
  exact height_one_localization_isDVR A U p hp

end H5OriginalDVR.Lane2.B1HeightOneLocalization
