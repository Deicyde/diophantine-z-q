/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy (AI-assisted)
-/
import ZInQKernel.Contrib.CloudB3W11AxCompletion.AxClosure
import ZInQKernel.Contrib.CloudB3W11AxCompletion.AxSenTateBridge

/-!
# The proved uniform input for the exact-target adapter

`UniformAxEstimates` was an explicit missing-input Prop in the original
completion bridge. Its witness is now an unconditional theorem, using B's
proved degree-independent `p²` estimate for every intermediate field.

The lead can supply this theorem to `axSenTate_of_uniformAxEstimates` in the
required new OneProof closing file. This supporting module does not create
or edit that closing file or the assembly, and performs no build-time checks.
-/

namespace ZInQ.Contrib.CloudB3W11AxCompletion

/-- The uniform arithmetic input required by the exact Ax–Sen–Tate adapter
is proved, with no remaining estimate hypothesis. -/
theorem uniformAxEstimates_proved : UniformAxEstimates := by
  intro p hp K hK
  exact ⟨(p : ℝ) ^ 2, sq_nonneg (p : ℝ), uniformAxApproximation_proved p K⟩

end ZInQ.Contrib.CloudB3W11AxCompletion
