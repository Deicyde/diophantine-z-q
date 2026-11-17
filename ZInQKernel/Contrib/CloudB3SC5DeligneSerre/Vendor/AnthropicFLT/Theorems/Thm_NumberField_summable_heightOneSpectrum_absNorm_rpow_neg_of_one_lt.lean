/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt (git blob b73299a0e51cb3377c00b9eaef3f7db4edad5039, sha256 28ea1b407fd52fa3131a3db8f2f816d79b6caa5c99c4ab23b61f3951c01a3325).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField IsDedekindDomain

-- [port] Mathlib 4.35 `Ideal.absNorm` needs `Infinite (𝓞 F)` (a characteristic-zero ring is infinite); statement text unchanged
local instance (F : Type) [Field F] [NumberField F] : Infinite (𝓞 F) :=
  Infinite.of_injective (Nat.cast : ℕ → 𝓞 F) Nat.cast_injective

theorem NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
    (F : Type) [Field F] [NumberField F] {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) := by
  revert F σ hσ
  exact @_root_.P2MW.S_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt.solution
