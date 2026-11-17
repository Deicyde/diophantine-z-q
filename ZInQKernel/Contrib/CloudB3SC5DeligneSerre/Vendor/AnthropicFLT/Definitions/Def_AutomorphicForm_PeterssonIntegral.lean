/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AutomorphicForm_PeterssonIntegral (git blob 30f04bb939aeeb518908b6d51880f1583bc96f7f, sha256 bb3113d8a7d1e86df43176779d2ecf10e2dad25b2825b7ad27d3a6c72e9084fc).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicHaar

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def peterssonIntegral (s : ℝ) (S : Set (AdelicGL2 (𝓞 F) F)) (x y : AdelicGL2 (𝓞 F) F → ℂ) : ℂ :=
  letI := glBorel (Fin 2) (𝓞 F) F
  ∫ g in S,
    x g * (starRingEnd ℂ) (y g) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ)
    ∂(adelicGLHaar (Fin 2) (𝓞 F) F)

end AutomorphicForm

end
