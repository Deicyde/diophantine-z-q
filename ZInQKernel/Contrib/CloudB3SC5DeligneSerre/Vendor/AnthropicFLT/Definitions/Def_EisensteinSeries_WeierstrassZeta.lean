/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_EisensteinSeries_WeierstrassZeta (git blob 8a95f170ed4d6bbabc09a533beb785e6da31f5c9, sha256 aaeb5b177a02db2655028f6ca5b550841b5490291646fb6868b53a54513ac3c9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace EisensteinSeries

noncomputable def weierstrassZeta (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  1 / z + ∑' v : Fin 2 → ℤ, if v = 0 then 0 else
    (1 / (z - ((v 0 : ℂ) * τ + v 1)) + 1 / ((v 0 : ℂ) * τ + v 1) + z / ((v 0 : ℂ) * τ + v 1) ^ 2)

noncomputable def eisensteinG1 (N : ℕ) (v : Fin 2 → ℤ) (τ : UpperHalfPlane) : ℂ :=
  1 / (N : ℂ) *
    (weierstrassZeta τ (((v 0 : ℂ) * τ + v 1) / N) -
      ((v 0 : ℂ) * ((τ : ℂ) * G2 τ - 2 * Real.pi * Complex.I) + (v 1 : ℂ) * G2 τ) / N)

end EisensteinSeries
