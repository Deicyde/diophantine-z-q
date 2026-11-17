/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/NumberTheory/NumberField/AutomorphismAction.lean
Original SHA-256: 7bc1306aed08f83919f7d206bbb1d6bb2b1f8e9f642974f7803ec8b77dd4601c
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
TauCeti/NumberTheory/NumberField/AutomorphismAction.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.NumberTheory.NumberField.Basic
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

open scoped NumberField

namespace NumberField

variable {R K : Type*} [CommSemiring R] [Field K] [Algebra R K]

/- **`algebraMap` intertwines the automorphism actions on `𝓞 K` and on `K`.** The action on the
ring of integers is the restriction of the action on `K` (`integralClosure.coe_smul`), so the
structure map sends `σ • z` to `σ` applied to the image of `z`.

Not named `algebraMap_smul`: that is Mathlib's unrelated `algebraMap R A r • m = r • m`. -/
@[simp] theorem algebraMap_smul_eq_apply (σ : K ≃ₐ[R] K) (z : 𝓞 K) :
    algebraMap (𝓞 K) K (σ • z) = σ (algebraMap (𝓞 K) K z) :=
  -- `integralClosure.coe_smul` proves this up to two definitional identifications:
  -- `RingOfIntegers.val` is an `abbrev` for `algebraMap`, and `AlgEquiv.smul_def` is `rfl`.
  integralClosure.coe_smul σ z

variable {M L : Type*} [Field M] [Field L] [Algebra K M] [Algebra M L] [Algebra K L]
  [IsScalarTower K M L] [Normal K M]

/- **Restriction of automorphisms commutes with the map between rings of integers.** If `M/K`
is normal inside `L`, then acting on `𝓞 M` by the restriction of `σ ∈ Gal(L/K)` and mapping to
`𝓞 L` agrees with first mapping and then acting by `σ`. -/
variable {F : Type*} [Field F] [Algebra K F]

/- **The Galois action on `𝓞 F` commutes with the `𝓞 K`-action.** A `K`-algebra automorphism of
`F` fixes `K` pointwise, so it fixes the image of `𝓞 K` in `F` and therefore commutes with
multiplication by it.

This is the relative form of Mathlib's `SMulCommClass G R (integralClosure R K)`, which for
`𝓞 F = integralClosure ℤ F` gives only the base ring `ℤ`. Neither field has to be a number
field. -/
end NumberField

namespace AlgEquiv

variable {R K L : Type*} [Field R] [Field K] [Field L] [Algebra R K] [Algebra R L]

/- Restriction to rings of integers intertwines conjugation of automorphisms along an algebra
equivalence. -/
end AlgEquiv
