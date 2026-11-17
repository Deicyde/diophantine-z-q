/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/NumberTheory/LocalField/Different/Basic.lean
Original SHA-256: 477f43bfa8ec9d1f990b41344cc4c9e3ad25b264d9d83f912928a7606194a74d
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
TauCeti/NumberTheory/LocalField/Different/Basic.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Unramified.LocalRing
import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.InertiaDegree
import Mathlib.RingTheory.LocalRing.Quotient
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DedekindDomain.Different.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

noncomputable section

section
noncomputable section

open ValuativeRel IsLocalRing

namespace TauCeti

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

section FractionRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/- Separability of `L / K` transported to the canonical fraction fields of `𝒪[K]` and `𝒪[L]`,
which is the form of the hypothesis taken by Mathlib's theory of the different ideal. -/
instance isSeparable_fractionRing_integerRing [Algebra.IsSeparable K L] :
    Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing 𝒪[L]) := by
  have := isLocalization_integerRing K L
  refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv 𝒪[K] K).symm.toRingEquiv
    (FractionRing.algEquiv 𝒪[L] L).symm.toRingEquiv ?_
  apply IsLocalization.ringHom_ext (nonZeroDivisors 𝒪[K])
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv,
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  rw [IsScalarTower.algebraMap_apply 𝒪[K] 𝒪[L] L, AlgEquiv.commutes,
    ← IsScalarTower.algebraMap_apply]

end FractionRing

/- The different exponent `d(L/K)` of an extension of nonarchimedean local fields: the
multiplicity of the maximal ideal of `𝒪[L]` in the different ideal `differentIdeal 𝒪[K] 𝒪[L]`.
For `L/K` separable the different ideal is `𝓂[L] ^ d(L/K)`, by
`differentIdeal_eq_maximalIdeal_pow`. -/
def differentExponent : ℕ :=
  multiplicity 𝓂[L] (differentIdeal 𝒪[K] 𝒪[L])

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/- The defining formula of `differentExponent`. -/
theorem differentExponent_def :
    differentExponent K L = multiplicity 𝓂[L] (differentIdeal 𝒪[K] 𝒪[L]) := (rfl)

variable [Algebra.IsSeparable K L]

/- **The characteristic property of the different exponent**: the `n`-th power of the maximal
ideal of `𝒪[L]` divides the different ideal exactly when `n ≤ d(L/K)`. -/
end TauCeti
