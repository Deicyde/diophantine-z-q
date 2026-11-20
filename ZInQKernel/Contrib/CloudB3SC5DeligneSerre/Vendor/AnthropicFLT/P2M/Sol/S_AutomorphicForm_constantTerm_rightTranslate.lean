/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_constantTerm_rightTranslate (git blob 3c6396f66d9c22ec639a7e4465ced8031be47d4c, sha256 11c14b989bda1b21923a55746051d6b75176ebce76979f31a951c4f5c533b2fd).
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

namespace P2MW.S_AutomorphicForm_constantTerm_rightTranslate
open AutomorphicForm MeasureTheory

theorem solution {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : Measure Q) (u : Q → G) (f : G → ℂ) (g h : G) :
    constantTerm μ u (fun x => f (x * h)) g = constantTerm μ u f (g * h) := by
  simp only [constantTerm, constantTermIntegrand, mul_assoc]
