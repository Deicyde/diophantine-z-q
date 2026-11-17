/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_nonempty_modularPolynomialData_of_squarefree (git blob 3a40062298496f291f1b3248ddd56e452a31a969, sha256 002f2d3731e3fab3ef950af18da2a9fdeda9cacca1290e7b648bb6a2ab407dcd).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_nonempty_modularPolynomialData_of_squarefree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve
theorem ModularCurve.nonempty_modularPolynomialData_of_squarefree (N : ℕ) [NeZero N] (hsf : Squarefree N) (hN : 1 < N) : Nonempty (ModularPolynomialData N) := by
  revert N hsf hN
  exact @_root_.P2MW.S_ModularCurve_nonempty_modularPolynomialData_of_squarefree.solution
