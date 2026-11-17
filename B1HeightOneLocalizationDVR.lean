/-
H5 Step2 / B1 KEY L3: height-one native localization is a DVR.
Copyright (c) 2026 H5 contributors. Apache-2.0.
SOURCE ONLY / UNCOMPILED. Native/kernel/BI/Std3/current-context grade absent.

Exact consumer read FULL73 lines: Step2B1/LocalizedComapInterface.lean3620B,
SHAf74bd5284d7b83d66223997f55392b01be86ef56cc3b90902ff89052bb72da01.
The older LocalizedComapPlan3d7616 has only prose L3/L4 and genuine L2;
L2's DVR ideal-automorphism proof is SINGLE and is not duplicated here.

TRUTH PRE-CHECK: a regular one-dimensional Noetherian local DOMAIN is a
DVR (Mathlib TFAE/cotangent criterion228–234). A2 proves every original
stalk regular. Actual affine/stalk localization maps give regularity of
Gamma(U), hence Gamma(U)_p. The exact prime height gives ring dimension1,
not a dimension cap on A. AV geometric integrality and p∈Spec Gamma(U)
give a nonempty U and the required ACTUAL domain structure; neither is
installed as a desired Fact. Fields/dimension0 have no height-one p;
a singular height-one local domain need not be DVR and is excluded by A2.

This proof deliberately uses the native cotangent criterion, NOT the heavy
regular-local UFD/finite-PD supplier or a generic A1 premise. Native TauCeti
all-stalk regularity and C5 A2 are SINGLE read-only Source suppliers. No
Stacks framework, generic localization/rank Factory, completion, CharZero,
perfectness, Type0 transfer or new numeric/transparency/budget option.
Original symbolic u, group A, affine U, prime p and algebraMap/localization
are literal. No edit to C3/C5/W07/TauCeti/fork; no Native/parser/helper/AST.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.LocalizedComapInterface
import I0SmoothFieldStalkRegular
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
  have hηU : U.2.fromSpec p ∈ U.1 := by
    rw [← U.2.range_fromSpec]
    exact ⟨p, rfl⟩
  letI : Nonempty U.1 := ⟨⟨U.2.fromSpec p, hηU⟩⟩
  letI : IsDomain Γ(A.X.left, U.1) := inferInstance
  letI : IsNoetherianRing Γ(A.X.left, U.1) :=
    IsLocallyNoetherian.component_noetherian U
  letI : IsRegularRing Γ(A.X.left, U.1) :=
    (TauCeti.AlgebraicGeometry.isRegularRing_iff_isRegularLocalRing_stalk U.2).mpr
      (fun x _ => H5OriginalDVR.Lane5.I0Native.smoothFieldStalkRegular A.X.hom x)
  let L := Localization.AtPrime p.asIdeal
  letI : IsDomain L := inferInstance
  letI : IsRegularLocalRing L := inferInstance
  have hDim : ringKrullDim L = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal L, hp]
  exact ⟨inferInstance, regularLocal_dimOne_isDVR L hDim⟩

/-- EXACT frozen consumer Prop, with no A1/UFD/localization/regularity Fact
or extra proof argument. Source-only until C6/default/runtime admission. -/
theorem heightOneLocalizationDVR :
    ZInQ.Contrib.CloudR2NOS.Step2B1.HeightOneLocalizationDVR.{u} := by
  intro K _ _ A _ U p hp
  exact height_one_localization_isDVR A U p hp

end H5OriginalDVR.Lane2.B1HeightOneLocalization
