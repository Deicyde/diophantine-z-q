-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.RingTheory.RegularLocalRing.Localization), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Localizations of regular rings

Localizing a regular ring preserves regularity.
-/

instance IsRegularRing.localization {R : Type*} [CommRing R] [IsRegularRing R] (M : Submonoid R) :
    IsRegularRing (Localization M) := by
  rw [isRegularRing_iff]
  intro p _
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M p).toRingEquiv
