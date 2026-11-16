-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.RingTheory.Spectrum.Prime.Cardinality), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Cardinality of a finite algebra spectrum

The number of prime ideals of a finite-dimensional algebra over a field is
bounded by its vector-space dimension.
-/

noncomputable section

/-- A finite-dimensional algebra over a field has at most as many prime ideals as its
dimension. -/
lemma IsArtinianRing.card_primeSpectrum_le_finrank (K A : Type*) [Field K] [CommRing A]
    [Algebra K A] [Module.Finite K A] :
    Nat.card (PrimeSpectrum A) ≤ Module.finrank K A := by
  have : IsArtinianRing A := .of_finite K A
  have := Fintype.ofFinite (PrimeSpectrum A)
  rw [Nat.card_eq_fintype_card, IsArtinianRing.finrank_eq_sum_primeSpectrum (R := A) K,
    Fintype.card_eq_sum_ones]
  refine Finset.sum_le_sum fun p _ ↦ ?_
  have : Module.Finite K (Localization.AtPrime p.asIdeal) :=
    .of_surjective (Algebra.algHom K A (Localization.AtPrime p.asIdeal)).toLinearMap
      (localization_surjective p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal))
  exact Module.finrank_pos
