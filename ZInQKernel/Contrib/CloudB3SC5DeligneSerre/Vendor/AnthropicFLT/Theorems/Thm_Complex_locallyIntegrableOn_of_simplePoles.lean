/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Complex_locallyIntegrableOn_of_simplePoles (git blob efb564553e69b0d6a2b7e730f5e19327ef675ae5, sha256 2e1b3243c9631207c4dd900ce8c7ab74ab0bd4012b5e5571cbdcbacd6fcb3dfa).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Complex_locallyIntegrableOn_of_simplePoles

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Complex MeasureTheory
open scoped Topology

theorem Complex.locallyIntegrableOn_of_simplePoles
    (U : Set ℂ) (hU : IsOpen U) (F c : ℂ → ℂ)
    (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z) :
    LocallyIntegrableOn F U := by
  revert U hU F c hloc
  exact @_root_.P2MW.S_Complex_locallyIntegrableOn_of_simplePoles.solution
