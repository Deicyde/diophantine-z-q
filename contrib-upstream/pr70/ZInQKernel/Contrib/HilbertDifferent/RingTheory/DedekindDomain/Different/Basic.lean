/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/DedekindDomain/Different/Basic.lean
Original SHA-256: 83ec4fed4c0e3a8d4e6df75150f0e9065d61fadf2abc71f4b3f836793e6d37cd
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
TauCeti/RingTheory/DedekindDomain/Different/Basic.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.RingTheory.DedekindDomain.Different
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

open Module

open scoped nonZeroDivisors

namespace TauCeti

section Multiplicity

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]
variable [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

/- The characteristic property of the different exponent at a nonzero prime `P` of `B`: `P ^ n`
divides the different ideal exactly when `n` is at most the multiplicity of `P` in it. -/
end Multiplicity

universe uR uS uK uL

variable {R : Type uR} {S : Type uS} {K : Type uK} {L : Type uL}
variable [CommRing R] [CommRing S] [Field K] [Field L]
variable [Algebra R S] [Algebra R K] [Algebra K L] [Algebra R L] [Algebra S L]
variable [IsScalarTower R K L] [IsScalarTower R S L]
variable [IsDomain R]
variable [IsFractionRing R K] [IsFractionRing S L]
variable [IsIntegrallyClosed R] [IsIntegralClosure S R L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

namespace FractionalIdeal

/- Over a domain, the fractional-ideal trace dual of one coerces to the submodule trace dual. -/
@[simp]
theorem coe_dual_one_of_isDomain [IsDomain S] :
    (↑(FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)) : Submodule S L) =
      Submodule.traceDual R K (1 : Submodule S L) := by
  ext x
  -- Rewriting through `FractionalIdeal.coe_mk` directly requires Mathlib's transparency override.
  -- Extensionality reduces the coercion equality to the definitionally equal membership predicates.
  change x ∈ FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L) ↔ _
  have h : (1 : FractionalIdeal S⁰ L) ≠ 0 := one_ne_zero
  simp [FractionalIdeal.dual, h]
  -- In the nonzero branch, `dual` stores the trace-dual submodule itself; only its proof field is
  -- discarded by the coercion, so the two remaining membership predicates are definitionally equal.
  rfl

end FractionalIdeal

/- **The trace dual of `S` is the inverse of the different ideal, elementwise**: an element of
`L` has integral traces against `S` exactly when it multiplies the different ideal of `S / R`
into `S`. -/
section TraceCriterion

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]

/- **The trace criterion for divisibility of the different ideal.** If `I * Q = p · B` for a
nonzero ideal `p` of `A`, then `I` divides `differentIdeal A B` exactly when the integral trace
carries the complement `Q` into `p`.

This upgrades Mathlib's one-way `not_dvd_differentIdeal_of_intTrace_not_mem` to an equivalence.
The converse direction adapts the argument that Mathlib runs inline in
`pow_sub_one_dvd_differentIdeal_aux` and `dvd_differentIdeal_of_not_isSeparable`
(`Mathlib/RingTheory/DedekindDomain/Different.lean`, Andrew Yang). -/
end TraceCriterion

variable {A : Type*} [CommRing A] [IsDomain A]

/- The trace dual of the unit submodule is the unit submodule for the identity extension of a
domain to its fraction field. -/
variable {D : Type*} [CommRing D] [IsDedekindDomain D]

/- The different ideal of the identity extension of a Dedekind domain is the unit ideal. -/
end TauCeti

end
