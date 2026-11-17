/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/Localization/Finiteness.lean
Original SHA-256: 2379c4f34fd5e95d5ac16d4ef1ba0e95c9abbc180221992bb575ad390faaaa74
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
TauCeti/RingTheory/Localization/Finiteness.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.RingTheory.Localization.Finiteness
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

namespace LinearMap

variable {A K B L : Type*} [CommSemiring A] [CommSemiring K] [Algebra A K]
  [AddCommMonoid B] [AddCommMonoid L] [Module A B] [Module A L] [Module K L]
  [IsScalarTower A K L]

/- If an injective linear map sends `x` into the span over a localization of the image of `s`,
then a multiple of `x` by an element of the localizing submonoid lies in the original span
of `s`. -/
theorem exists_smul_mem_span_of_apply_mem_span_image (f : B →ₗ[A] L) (hf : Function.Injective f)
    (M : Submonoid A) [IsLocalization M K] (s : Set B) (x : B)
    (hx : f x ∈ Submodule.span K (f '' s)) :
    ∃ a ∈ M, a • x ∈ Submodule.span A s := by
  obtain ⟨⟨a, ha⟩, hax⟩ := multiple_mem_span_of_mem_localization_span M K (f '' s) (f x) hx
  refine ⟨a, ha, (Submodule.apply_mem_span_image_iff_mem_span hf).mp ?_⟩
  simpa only [map_smul, Submonoid.smul_def] using hax

end LinearMap

end
