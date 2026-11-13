/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Ported for the T18 contribution from TauCetiProject/TauCeti@1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Analysis/Fourier/Integrable.lean. Changes: imports relocated to the owned flat contribution directory;
proof and definition bodies initially unchanged. Project pins are not changed.
See docs/research/t18-frobenius-density.md for attribution and license text.
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Integrability of Fourier transforms of smooth compactly supported functions

A smooth compactly supported function is a Schwartz function, so its Fourier transform is also a
Schwartz function and hence integrable. This supplies the Fourier-integrability hypotheses needed
in dominated-convergence arguments, such as the Wiener--Ikehara boundary identity.

## Main declarations

* `TauCeti.integrable_fourier_of_contDiff_of_hasCompactSupport`: the Fourier transform of a
  smooth compactly supported function on a finite-dimensional real inner product space is
  integrable.
-/

public section

open MeasureTheory
open scoped ContDiff FourierTransform

namespace TauCeti

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}

/-- The Fourier transform of a smooth compactly supported function is integrable. -/
theorem integrable_fourier_of_contDiff_of_hasCompactSupport (hf : ContDiff ℝ ∞ f)
    (hsupp : HasCompactSupport f) : Integrable (𝓕 f) := by
  have hcoe : ⇑(hsupp.toSchwartzMap hf) = f := by
    ext x
    simp
  have h : Integrable ((𝓕 (hsupp.toSchwartzMap hf) : SchwartzMap V E) : V → E) :=
    SchwartzMap.integrable _
  rwa [SchwartzMap.fourier_coe, hcoe] at h

end TauCeti
