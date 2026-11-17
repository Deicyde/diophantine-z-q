/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/DedekindDomain/AdicValuation/RamificationIndex.lean
Original SHA-256: 9716a2c4427be037100bf7460ebc0fcac19dfb438b863a5b62089c7b735dc55a
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
TauCeti/RingTheory/DedekindDomain/AdicValuation/RamificationIndex.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.RamificationIndex
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Unramified.LocalRing
import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.InertiaDegree
import Mathlib.RingTheory.LocalRing.Quotient
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DedekindDomain.AdicValuation.ValuativeExtension

noncomputable section

section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped AdicCompletionExtension

namespace IsDedekindDomain.HeightOneSpectrum

section Extension

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
  [Finite (R ⧸ v.asIdeal)] [Finite (B ⧸ w.asIdeal)]

private theorem normalizedValuationWithZero_adicCompletion_algebraMap
    (x : v.adicCompletion K) :
    TauCeti.normalizedValuationWithZero (w.adicCompletion L)
        (algebraMap (v.adicCompletion K) (w.adicCompletion L) x) =
      TauCeti.normalizedValuationWithZero (v.adicCompletion K) x ^
        v.asIdeal.ramificationIdx' w.asIdeal := by
  rw [normalizedValuationWithZero_adicCompletion,
    normalizedValuationWithZero_adicCompletion, algebraMap_adicCompletionExtensionAlgebra,
    valued_adicCompletionExtension, inv_pow]

/- **The local ramification index is the global one.** For `w` a height-one prime of `B` over the
height-one prime `v` of `R`, with finite residue fields, the ramification index of the extension
of local fields `L_w / K_v`, for the canonical algebra structure of `adicCompletionExtension`, is
the ramification index of `w` over `R`. -/
@[simp]
theorem ramificationIndex_adicCompletion :
    TauCeti.ramificationIndex (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.ramificationIdx R := by
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
  refine TauCeti.ramificationIndex_eq_iff.2 fun x ↦ WithZero.coe_injective ?_
  simpa only [WithZero.coe_pow, ← TauCeti.normalizedValuationWithZero_coe,
    Units.coe_map, MonoidHom.coe_ofClass] using
      normalizedValuationWithZero_adicCompletion_algebraMap v w (x : v.adicCompletion K)

/- **Tameness of the completed extension.** The extension of local fields `L_w / K_v` is tamely
ramified exactly when the ramification index of `w` over `R` is nonzero in the residue field
`R ⧸ v`. -/

end Extension

end IsDedekindDomain.HeightOneSpectrum
