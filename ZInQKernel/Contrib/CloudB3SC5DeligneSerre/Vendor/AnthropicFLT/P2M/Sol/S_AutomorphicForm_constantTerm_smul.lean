/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_constantTerm_smul (git blob 3ab44b22a0f689337eaebe012f855ba8ca3ff2d4, sha256 717394640248943ff2effd76aa3c9a3291b48b537b2ae424b818b1459e07f6ba).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_constantTerm_smul
open AutomorphicForm MeasureTheory

theorem solution {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : Measure Q) (u : Q → G) (c : ℂ) (f : G → ℂ) (g : G) :
    constantTerm μ u (fun x => c * f x) g = c * constantTerm μ u f g := by
  simpa [constantTerm, constantTermIntegrand, smul_eq_mul] using
    integral_smul (μ := μ) c (fun q => f (u q * g))
