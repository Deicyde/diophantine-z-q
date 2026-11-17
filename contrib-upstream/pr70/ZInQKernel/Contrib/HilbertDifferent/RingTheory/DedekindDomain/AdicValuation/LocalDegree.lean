/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/DedekindDomain/AdicValuation/LocalDegree.lean
Original SHA-256: 7d0c3dc4aefe72caa0f70d02c3145dac2becc2a9a5cab1e2f6a63dc0332dbd26
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
TauCeti/RingTheory/DedekindDomain/AdicValuation/LocalDegree.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.InertiaDegree
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DedekindDomain.AdicValuation.InertiaDegree
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DedekindDomain.AdicValuation.RamificationIndex
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section
noncomputable section

open IsDedekindDomain
open scoped AdicCompletionExtension

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
  [Finite (B ⧸ w.asIdeal)]

/- **The local degree of a completion.** For `w` a height-one prime of `B` over the height-one
prime `v` of `R`, with finite residue field, the degree of `L_w` over `K_v` for the canonical
algebra structure of `adicCompletionExtension` is the product of the ramification index and the
inertia degree of `w` over `R`. -/
@[simp]
theorem finrank_adicCompletion :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.ramificationIdx R * w.asIdeal.inertiaDeg R := by
  -- the residue field of `v` embeds in the residue field of `w`, so it is finite too
  have : Finite (R ⧸ v.asIdeal) :=
    .of_injective _ (FaithfulSMul.algebraMap_injective (R ⧸ v.asIdeal) (B ⧸ w.asIdeal))
  rw [← TauCeti.ramificationIndex_mul_inertiaDegree (v.adicCompletion K) (w.adicCompletion L),
    ramificationIndex_adicCompletion, TauCeti.inertiaDegree_def,
    finrank_residueField_adicCompletion]

end IsDedekindDomain.HeightOneSpectrum
