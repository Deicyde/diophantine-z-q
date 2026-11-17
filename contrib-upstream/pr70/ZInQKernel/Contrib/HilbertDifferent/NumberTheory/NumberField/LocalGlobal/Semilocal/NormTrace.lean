/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/NumberTheory/NumberField/LocalGlobal/Semilocal/NormTrace.lean
Original SHA-256: 96ea50c763ebefe1c3b8db418610c5a8636845775a4965170319b63653e38243
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
TauCeti/NumberTheory/NumberField/LocalGlobal/Semilocal/NormTrace.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic
import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.NumberField.LocalGlobal.Semilocal.Integers
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.NormTrace.Pi
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.NormTrace.BaseChange
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

namespace TauCeti

open IsDedekindDomain NumberField Module

open scoped TensorProduct NumberField AdicCompletionExtension Valued BigOperators

universe u v

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K : Type u} [Field K] [NumberField K]
variable (L : Type v) [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝒪 K))

/- The trace of a pure integral tensor paired with a global element is a scalar extension of
the global trace pairing. -/
theorem trace_integralSemilocalToField_tmul_mul
    (a : v.adicCompletionIntegers K) (x : 𝒪 L) (d : L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
        (integralSemilocalToField L v (a ⊗ₜ x) * (1 ⊗ₜ d)) =
      (a : v.adicCompletion K) *
        algebraMap K (v.adicCompletion K) (Algebra.trace K L ((x : L) * d)) := by
  have ha : (a : v.adicCompletion K) ⊗ₜ[K] ((x : L) * d) =
      (a : v.adicCompletion K) • ((1 : v.adicCompletion K) ⊗ₜ[K] ((x : L) * d)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [integralSemilocalToField_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ha,
    map_smul, Algebra.trace_baseChange_tmul, smul_eq_mul]

attribute [local instance] Fintype.ofFinite in
/- The trace of the semilocal algebra `K_v ⊗[K] L` over `K_v` is the sum of the traces of the
components of the semilocal decomposition. -/
@[simp] theorem trace_eq_sum_trace_semilocalEquiv (ξ : v.adicCompletion K ⊗[K] L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) ξ =
      ∑ w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L) (semilocalEquiv L v ξ w) := by
  rw [← Algebra.trace_eq_of_algEquiv (semilocalEquiv L v)]
  exact Algebra.trace_pi _

open scoped Classical in
attribute [local instance] Fintype.ofFinite in
/- An element of `L_w`, placed in the `w`-component of `K_v ⊗[K] L`, has the same trace pairing
with a global element as in `L_w`. -/
theorem trace_semilocalEquiv_symm_single_mul
    (w : HeightOneSpectrum (𝒪 L)) [w.asIdeal.LiesOver v.asIdeal]
    (z : w.adicCompletion L) (x : L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
        ((semilocalEquiv L v).symm (Pi.single (⟨w, inferInstance⟩ :
          {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) z) * (1 ⊗ₜ x)) =
      Algebra.trace (v.adicCompletion K) (w.adicCompletion L)
        (z * algebraMap L (w.adicCompletion L) x) := by
  classical
  rw [trace_eq_sum_trace_semilocalEquiv, Finset.sum_eq_single
    (⟨w, inferInstance⟩ : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal})]
  · simp [semilocalEquiv_tmul]
  · intro w' _ hw'
    simp [Pi.single_eq_of_ne hw']
  · simp

end TauCeti
