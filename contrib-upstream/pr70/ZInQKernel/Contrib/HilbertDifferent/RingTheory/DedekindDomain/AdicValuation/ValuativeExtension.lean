/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/DedekindDomain/AdicValuation/ValuativeExtension.lean
Original SHA-256: 7e54917388bf8309d2d903c30825e913a03462f1be1413c79a0df7de4790edb4
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- Adapted to the repository-pinned Mathlib API; only declarations needed by the
Hilbert different consumer are retained. Source: TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/RingTheory/DedekindDomain/AdicValuation/ValuativeExtension.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DedekindDomain.AdicCompletionExtension
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section
noncomputable section

open ValuativeRel
open scoped AdicCompletionExtension WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

variable (K L) in
/- The canonical map `K_v → L_w` preserves and reflects the valuative relations induced by the
adic valuations. -/
@[simp] theorem adicCompletionExtension_vle_iff_vle (a b : v.adicCompletion K) :
    adicCompletionExtension K L v w a ≤ᵥ adicCompletionExtension K L v w b ↔ a ≤ᵥ b := by
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  rw [Valuation.vle_iff_le (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰),
    Valuation.vle_iff_le (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰),
    valued_adicCompletionExtension, valued_adicCompletionExtension]
  exact pow_le_pow_iff_left₀ zero_le zero_le
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot)

/- The completion `L_w` of `L` above `v` is a valuative extension of `K_v`, for the canonical
algebra structure given by `adicCompletionExtension`. -/
theorem completionValuativeExtension :
    ValuativeExtension (v.adicCompletion K) (w.adicCompletion L) where
  vle_iff_vle a b := by
    rw [algebraMap_adicCompletionExtensionAlgebra]
    exact adicCompletionExtension_vle_iff_vle K L v w a b

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.completionValuativeExtension

end IsDedekindDomain.HeightOneSpectrum
