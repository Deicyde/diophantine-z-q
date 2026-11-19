/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_rightConv_rightTranslate_mem_of_isCuspSubrep (git blob 7b5dc12fcc6d82a3df2fd36a0b4ddfe4e752d237, sha256 d88667ef20e640857c5a3897a64515728c1eb2498fdd9c2c8805d87176bcd416).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_rightConv_rightTranslate_mem_of_isCuspSubrep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.rightConv_rightTranslate_mem_of_isCuspSubrep
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspSubrep F pins ξ V)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ V)
    (h : AdelicGL2 (𝓞 F) F) (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsFactorizableTestFn F f) (hft : IsArchBiFinite F tys f) :
    rightConv F (rightTranslate F h φ) f ∈ V := by
  revert F pins ξ tys V hV φ hφ h f hf hft
  exact @_root_.P2MW.S_AutomorphicForm_rightConv_rightTranslate_mem_of_isCuspSubrep.solution
