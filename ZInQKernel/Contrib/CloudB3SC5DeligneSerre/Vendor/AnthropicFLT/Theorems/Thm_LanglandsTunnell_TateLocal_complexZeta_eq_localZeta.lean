/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_TateLocal_complexZeta_eq_localZeta (git blob 6a18a76a78fe355f713f0d8237de019e10d3092b, sha256 44e2ec860482a68b0c361d59a8042a23c74ce9e5936375754d63291f19d9d002).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_ArchPlace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_TateLocal_complexZeta_eq_localZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
open MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped NNReal

theorem LanglandsTunnell.TateLocal.complexZeta_eq_localZeta
    (μ : Measure ℂ) (f : ℂ → ℂ) (χ : ℂˣ →* ℂˣ) (s : ℂ) :
    complexZeta μ f χ s = localZeta μ f χ s := by
  revert μ f χ s
  exact @_root_.P2MW.S_LanglandsTunnell_TateLocal_complexZeta_eq_localZeta.solution
