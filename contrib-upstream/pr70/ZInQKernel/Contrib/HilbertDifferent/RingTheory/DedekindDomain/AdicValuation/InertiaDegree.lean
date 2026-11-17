/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/DedekindDomain/AdicValuation/InertiaDegree.lean
Original SHA-256: f42280a93540ebf87e6679ee2e192386c44960dc86a4c673b5e13a832aa443d9
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
TauCeti/RingTheory/DedekindDomain/AdicValuation/InertiaDegree.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.RingTheory.RamificationInertia.Inertia
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DedekindDomain.AdicValuation.ValuativeExtension
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.Valuation.ValuativeRel.Extension
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section
noncomputable section

open IsDedekindDomain
open scoped AdicCompletionExtension ValuativeRel

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

/- **The residue-field identifications are natural.** The identifications `R ⧸ v ≃+* 𝓀[K_v]` and
`B ⧸ w ≃+* 𝓀[L_w]` intertwine the residue extension of `w` over `v` with the residue extension of
the completions. -/
@[simp]
theorem algebraMap_residueFieldEquivAdicCompletion (x : R ⧸ v.asIdeal) :
    algebraMap 𝓀[v.adicCompletion K] 𝓀[w.adicCompletion L]
        (v.residueFieldEquivAdicCompletion (K := K) x) =
      w.residueFieldEquivAdicCompletion (K := L)
        (algebraMap (R ⧸ v.asIdeal) (B ⧸ w.asIdeal) x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver, residueFieldEquivAdicCompletion_apply_mk,
    residueFieldEquivAdicCompletion_apply_mk, IsLocalRing.ResidueField.algebraMap_residue]
  refine congrArg (IsLocalRing.residue _) (Subtype.ext ?_)
  rw [TauCeti.coe_algebraMap_integerRing, algebraMap_adicCompletionExtensionAlgebra]
  exact adicCompletionExtension_algebraMap K L v w a

/- **The local residue degree is the global inertia degree.** For `w` a height-one prime of `B`
over the height-one prime `v` of `R`, the residue field of the completion `L_w` has degree
`w.asIdeal.inertiaDeg R` over the residue field of `K_v`. -/
@[simp]
theorem finrank_residueField_adicCompletion :
    Module.finrank 𝓀[v.adicCompletion K] 𝓀[w.adicCompletion L] =
      w.asIdeal.inertiaDeg R := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
  refine (Algebra.finrank_eq_of_equiv_equiv (v.residueFieldEquivAdicCompletion (K := K))
    (w.residueFieldEquivAdicCompletion (K := L)) (RingHom.ext fun x ↦ ?_)).symm
  exact algebraMap_residueFieldEquivAdicCompletion v w x

/- **The residue cardinality of a completion.** When the residue field of `w` is finite, the
residue field of `L_w` has `#𝓀[K_v] ^ f(w ∣ v)` elements. -/
end IsDedekindDomain.HeightOneSpectrum
