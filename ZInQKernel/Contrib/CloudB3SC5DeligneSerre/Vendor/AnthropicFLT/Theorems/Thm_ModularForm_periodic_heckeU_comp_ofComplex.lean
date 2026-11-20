/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_periodic_heckeU_comp_ofComplex (git blob 810fb6847080788f440f42c4f5b0ebac48478f61, sha256 6ea3e95008ac57d0bfa41c48bc6bd939d18ca1d4bf907acdb7baa770c6f4ebdb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_periodic_heckeU_comp_ofComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularForm.periodic_heckeU_comp_ofComplex {f : UpperHalfPlane → ℂ} (hf : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (k : ℤ) (p : ℕ) : Function.Periodic (ModularForm.heckeU k p f ∘ UpperHalfPlane.ofComplex) 1 := by
  revert f hf k p
  exact @_root_.P2MW.S_ModularForm_periodic_heckeU_comp_ofComplex.solution
