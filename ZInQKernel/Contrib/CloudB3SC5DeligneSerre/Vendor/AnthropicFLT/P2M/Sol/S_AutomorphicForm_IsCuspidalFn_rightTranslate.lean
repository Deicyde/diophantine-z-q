/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_IsCuspidalFn_rightTranslate (git blob 4bcd1de3b8cf18bd0f1f85cc1c28b2e427d3ee26, sha256 dba1d9e64f4d4d5d599784fb65e71ffca063d2285b44983839cff217764a32de).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_constantTerm_rightTranslate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_IsCuspidalFn_rightTranslate
open AutomorphicForm MeasureTheory

theorem solution {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : Measure Q} {u : Q → G} {f : G → ℂ}
    (hf : IsCuspidalFn μ u f) (h : G) : IsCuspidalFn μ u (fun x => f (x * h)) :=
  fun g => by rw [constantTerm_rightTranslate]; exact hf (g * h)
