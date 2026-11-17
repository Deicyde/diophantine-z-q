/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent (git blob 503753db46d478baf4b835ea35e1c6da1f21e4b0, sha256 141ecdbad10ddfb86c817b90c0a09959910f304524783ae566841c89e583ef81).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_IwasawaShellIndex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm IsDedekindDomain
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : AdelicGL2 (𝓞 K) K) (hx : x ∈ rationalCentreUnipotent K) (g : AdelicGL2 (𝓞 K) K) :
    iwasawaShellIndex K v (x * g) = iwasawaShellIndex K v g := by
  revert K v x hx g
  exact @_root_.P2MW.S_AutomorphicForm_iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent.solution
