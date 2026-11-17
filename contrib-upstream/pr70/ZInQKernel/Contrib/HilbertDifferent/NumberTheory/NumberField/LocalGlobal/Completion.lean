/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/NumberTheory/NumberField/LocalGlobal/Completion.lean
Original SHA-256: 4d8fcb41a76ef12db1551004dd119e8257946cbf6ecee99691e8c678dfa8fab5
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
TauCeti/NumberTheory/NumberField/LocalGlobal/Completion.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DedekindDomain.AdicValuation.ValuativeExtension
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section
noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField AdicCompletionExtension

namespace IsDedekindDomain.HeightOneSpectrum

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]

/- The canonical map `K_v → L_w` for a finite place `w` of `L` above a finite place `v` of
`K`, as a `K`-algebra homomorphism. -/
def completionAlgHom {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    v.adicCompletion K →ₐ[K] w.adicCompletion L where
  toRingHom := v.adicCompletionExtension K L w
  commutes' x := v.adicCompletionExtension_coe K L w x

/- The algebra map of the canonical completion algebra is `completionAlgHom`. -/
-- Not `@[simp]`: `algebraMap_adicCompletionExtensionAlgebra` already simplifies the left-hand side
-- to the underlying `adicCompletionExtension`, so the `simpNF` linter rejects this wrapper theorem.
theorem algebraMap_eq_completionAlgHom {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) =
      (completionAlgHom v w).toRingHom := by
  rw [algebraMap_adicCompletionExtensionAlgebra]
  -- The `toRingHom` field of the number-field wrapper is the generic completion extension.
  rfl

/- The canonical map between completions is continuous. -/
theorem continuous_completionAlgHom {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    Continuous (completionAlgHom v w) :=
  v.continuous_adicCompletionExtension K L w

/- A continuous ring homomorphism `K_v → L_w` extending `K → L` is the canonical completion
map. -/
theorem eq_completionAlgHom_of_continuous {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (f : v.adicCompletion K →+* w.adicCompletion L) (hf : Continuous f)
    (hcomp : ∀ x : K, f (algebraMap K (v.adicCompletion K) x) =
      algebraMap L (w.adicCompletion L) (algebraMap K L x)) :
    f = (completionAlgHom v w).toRingHom :=
  v.eq_adicCompletionExtension_of_continuous K L w hf hcomp

/- The canonical map from a completion to itself is the identity. -/
theorem completionIsScalarTower {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [algebraMap_eq_completionAlgHom]
    exact ((completionAlgHom v w).commutes x).symm

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.completionIsScalarTower

/- Scalar multiplication by `K_v` on `L_w` is continuous for the canonical completion
algebra. -/
theorem completionContinuousSMul {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) := by
  apply continuousSMul_of_algebraMap
  rw [algebraMap_eq_completionAlgHom]
  exact continuous_completionAlgHom v w

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.completionContinuousSMul

/- Canonical completion maps compose in a tower of number fields. -/
end IsDedekindDomain.HeightOneSpectrum
