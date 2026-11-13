/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Ported for the T18 contribution from TauCetiProject/TauCeti@1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Analysis/Fourier/Continuous.lean. Changes: imports relocated to the owned flat contribution directory;
proof and definition bodies initially unchanged. Project pins are not changed.
See docs/research/t18-frobenius-density.md for attribution and license text.
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Continuity of the Fourier transform of an integrable function

On a finite-dimensional real inner-product space, the Fourier transform `𝓕 F` of an integrable
`F` is continuous, and so is the inverse transform `𝓕⁻ F = 𝓕 F ∘ (-·)`. These are Mathlib's
`VectorFourier.fourierIntegral_continuous` specialized to the inner-product pairing, packaged so
that consumers do not repeat the `innerₗ`/`continuous_inner` bridge at every call site.

Nothing here is specific to positive-definite functions or to the Bochner roadmap; the file sits
outside `TauCeti/Analysis/Bochner/` so that it can be used by any Fourier-analysis development.

## Main declarations

* `TauCeti.continuous_fourier_of_integrable`: `𝓕 F` is continuous for integrable `F`.
* `TauCeti.continuous_fourierInv_of_integrable`: `𝓕⁻ F` is continuous for integrable `F`.
-/

public section

open MeasureTheory
open scoped FourierTransform

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Fourier transform of an integrable function is continuous. This is Mathlib's
`VectorFourier.fourierIntegral_continuous` specialized to the inner-product pairing. -/
theorem continuous_fourier_of_integrable {F : V → ℂ} (hint : Integrable F) : Continuous (𝓕 F) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by simpa only [innerₗ_apply_apply] using continuous_inner) hint

/-- The inverse Fourier transform of an integrable function is continuous: it is the Fourier
transform precomposed with negation. -/
theorem continuous_fourierInv_of_integrable {F : V → ℂ} (hint : Integrable F) :
    Continuous (𝓕⁻ F) := by
  rw [funext fun ξ => Real.fourierInv_eq_fourier_neg F ξ]
  exact (continuous_fourier_of_integrable hint).comp continuous_neg

end TauCeti
