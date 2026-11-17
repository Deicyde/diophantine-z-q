/-
Copyright (c) 2026 H5 contributors. Apache-2.0.
Native universe-u producer for EXACT C2 A1 RegularLocalUFD.{u}.
SOURCE ONLY / UNCOMPILED. No supplied IsRegularRing, localization theorem,
Factory, dimension bound, field, characteristic or completion input.

Actual native W07 finite-projective-dimension and Serre-converse cores are
reused without copying, modifying their options or compiling their closure.
For every original prime p of R, R/p has finite projective dimension; the
actual localization functor and its base-change equivalence identify its
localization with the actual residue field of R_p. Thus R_p is regular by
Serre's native converse, so the native Mathlib IsRegularRing record is DERIVED.
Only then does the existing native regular-local/regular-ring UFD proof apply.
The latter's extra regular-ring hypothesis is not silently ignored.

No Stacks module or predicate bridge. Received c496 UniqueFactorization is
an attributed mathematical blueprint only; native c4254cce W07/Mathlib
LICENSE/NOTICE/headers and protected supplier bytes remain unchanged.
Any scoped supplier options remain a separately catalogued native-admission
question, not default-limit evidence or permission for conformance copies.
-/
import Step2DelegatedInterfaces
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.RingTheory.RegularLocalRing.UniqueFactorization
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Quotient

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace H5OriginalDVR.Lane5.I0Native

/-- Every ORIGINAL prime localization of a regular local ring is regular.
The residue-field equivalence is an actual B-linear composition, not a rank
or quotient-name identification and not a Type0 universe-transfer theorem. -/
theorem regularLocal_localization_regular
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (p : Ideal R) [p.IsPrime] : IsRegularLocalRing (Localization.AtPrime p) := by
  let B := Localization.AtPrime p
  letI : IsNoetherianRing B :=
    IsLocalization.isNoetherianRing p.primeCompl B inferInstance
  let M : ModuleCat.{u} R := ModuleCat.of R (R ⧸ p)
  obtain ⟨n, hn⟩ := IsRegularLocalRing.exists_hasProjectiveDimensionLE M
  letI : HasProjectiveDimensionLE M n := hn
  let F : ModuleCat.{u} B := M.localizedModule p.primeCompl
  letI : HasProjectiveDimensionLE F n :=
    ModuleCat.localizedModule_hasProjectiveDimensionLE n p.primeCompl M
  have hbc : IsBaseChange B (M.localizedModuleMkLinearMap p.primeCompl) :=
    IsLocalizedModule.isBaseChange p.primeCompl B
      (M.localizedModuleMkLinearMap p.primeCompl)
  let eqResidue :
      (B ⧸ p.map (algebraMap R B)) ≃ₗ[B] IsLocalRing.ResidueField B :=
    Submodule.quotEquivOfEq _ _ (IsLocalization.AtPrime.map_eq_maximalIdeal p B)
  let e : F ≃ₗ[B] IsLocalRing.ResidueField B :=
    hbc.equiv.symm ≪≫ₗ
      (Ideal.quotMapEquivTensorQuot (R := R) B (I := p)).symm ≪≫ₗ eqResidue
  have hκ : HasProjectiveDimensionLE
      (ModuleCat.of B (IsLocalRing.ResidueField B)) n :=
    ModuleCat.hasProjectiveDimensionLE_of_linearEquiv
      (M := F) (N := ModuleCat.of B (IsLocalRing.ResidueField B)) e n
  exact IsRegularLocalRing.of_hasProjectiveDimensionLE_residueField n hκ

/-- The missing regular-ring structure is constructed by its ACTUAL field. -/
theorem regularLocal_isRegularRing
    (R : Type u) [CommRing R] [IsRegularLocalRing R] : IsRegularRing R := by
  rw [isRegularRing_iff]
  intro p _
  exact regularLocal_localization_regular R p

/-- EXACT C2 A1; no stronger regular-ring hypothesis is input. -/
theorem regularLocalUFD :
    H5OriginalDVR.Lane2.Step2DelegatedInterfaces.RegularLocalUFD.{u} := by
  intro R _ _
  letI : IsRegularRing R := regularLocal_isRegularRing R
  exact IsRegularLocalRing.uniqueFactorizationMonoid R

end H5OriginalDVR.Lane5.I0Native
