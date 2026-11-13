/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Ported for the T18 contribution from TauCetiProject/TauCeti@1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Analysis/Asymptotics/InvSubOne.lean. Changes: imports relocated to the owned flat contribution directory;
proof and definition bodies initially unchanged. Project pins are not changed.
See docs/research/t18-frobenius-density.md for attribution and license text.
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Complex.Basic

/-!
# Growth `O((σ - 1)⁻¹)` from a one-sided limit of `(σ - 1) f(σ)`

If `(σ - 1) f(σ)` has a limit as the real variable `σ` tends to `1` from the right, then
`f(σ) = O((σ - 1)⁻¹)` there. This is how a bound of this shape is usually obtained for a
Dedekind zeta function or an `L`-series near `s = 1`, from the limit of `(s - 1) L(s)` along the
real axis.

## Main results

* `TauCeti.isBigO_inv_sub_one_of_tendsto_sub_one_mul`: if `(σ - 1) f(σ)` converges as `σ → 1⁺`,
  then `f(σ) = O((σ - 1)⁻¹)` as `σ → 1⁺`.

## References

* Mathlib's `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, by Michael Stoll and David
  Loeffler, derives the same bound for the Dirichlet `L`-function of the trivial character in
  `DirichletCharacter.LFunctionTrivChar_isBigO_near_one_horizontal`.
-/

public section

open Asymptotics Complex Filter
open scoped Topology

namespace TauCeti

/-- If `(σ - 1) f(σ)` has a limit as `σ → 1⁺` through real values, then `f(σ) = O((σ - 1)⁻¹)`
as `σ → 1⁺`. -/
theorem isBigO_inv_sub_one_of_tendsto_sub_one_mul {f : ℝ → ℂ} {r : ℂ}
    (h : Tendsto (fun σ : ℝ ↦ ((σ : ℂ) - 1) * f σ) (𝓝[>] 1) (𝓝 r)) :
    f =O[𝓝[>] 1] fun σ : ℝ ↦ (σ - 1)⁻¹ := by
  have hinv : (fun σ : ℝ ↦ ((σ : ℂ) - 1)⁻¹) =O[𝓝[>] 1] fun σ : ℝ ↦ (σ - 1)⁻¹ :=
    isBigO_of_le _ fun σ ↦ by rw [← ofReal_one, ← ofReal_sub, ← ofReal_inv, norm_real]
  refine ((h.isBigO_one ℝ).mul hinv).congr' ?_ (by simp)
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  have : (σ : ℂ) - 1 ≠ 0 := by
    rw [← ofReal_one, ← ofReal_sub, ofReal_ne_zero]
    exact sub_ne_zero.mpr hσ.ne'
  field_simp

end TauCeti
