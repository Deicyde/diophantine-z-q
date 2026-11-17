/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/AdicCompletion/Pi.lean
Original SHA-256: b0b6150bdfc92d8ca524bb2abecf0b5b8f042e43d3911f415ae927f7e06038fd
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
TauCeti/RingTheory/AdicCompletion/Pi.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.RingTheory.AdicCompletion.Functoriality
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

open AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R) {ι : Type*} (M : ι → Type*)
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/- The canonical map from a product to its adic completion, followed by the comparison map
`AdicCompletion.pi` to the product of the completions, is the product of the canonical maps of the
factors. -/
@[simp]
theorem AdicCompletion.pi_of (x : ∀ i, M i) (j : ι) :
    AdicCompletion.pi I M (of I (∀ i, M i) x) j = of I (M j) (x j) := by
  simp [AdicCompletion.pi, map_of]

/- A product of `I`-adically Hausdorff modules is `I`-adically Hausdorff. -/
instance IsPrecomplete.pi [Finite ι] [∀ i, IsPrecomplete I (M i)] : IsPrecomplete I (∀ i, M i) := by
  classical
  have := Fintype.ofFinite ι
  refine of_surjective_iff.mp fun y ↦ ?_
  choose x hx using fun j ↦ of_surjective I (M j) (AdicCompletion.pi I M y j)
  refine ⟨x, (piEquivOfFintype I M).injective (_root_.funext fun j ↦ ?_)⟩
  rw [piEquivOfFintype_apply, piEquivOfFintype_apply, pi_of, hx]

/- A finite product of `I`-adically complete modules is `I`-adically complete. -/
