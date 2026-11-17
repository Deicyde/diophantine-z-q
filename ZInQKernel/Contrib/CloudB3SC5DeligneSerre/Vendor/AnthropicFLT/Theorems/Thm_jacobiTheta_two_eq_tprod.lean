/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_jacobiTheta_two_eq_tprod (git blob 90fb65385ab7a7914504939f68efcdb7cc35d0f2, sha256 c2eb7a018cc4a4e4bfd8fb054b324862f130e6fae8a73ee9eae63a21ef7ff542).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_jacobiTheta_two_eq_tprod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped Real
open Complex
theorem jacobiTheta_two_eq_tprod (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta₂ z τ = ∏' n : ℕ,
      ((1 - Complex.exp (2 * π * I * (n + 1) * τ)) *
        (1 + Complex.exp (π * I * (2 * n + 1) * τ + 2 * π * I * z)) *
        (1 + Complex.exp (π * I * (2 * n + 1) * τ - 2 * π * I * z))) := by
  revert z τ hτ
  exact @_root_.P2MW.S_jacobiTheta_two_eq_tprod.solution
