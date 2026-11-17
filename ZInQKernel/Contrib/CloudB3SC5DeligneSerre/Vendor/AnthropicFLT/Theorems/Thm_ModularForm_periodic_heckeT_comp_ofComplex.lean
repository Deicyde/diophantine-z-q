/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_periodic_heckeT_comp_ofComplex (git blob 2e018b982db3db0a97ce16a253498ebe317387f5, sha256 3effadf081ca9ae265c5db65783a72acd7145f95893c8ca4d73db2e0944ba69c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_periodic_heckeT_comp_ofComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularForm.periodic_heckeT_comp_ofComplex {f : UpperHalfPlane → ℂ} (hf : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (k : ℤ) (p : ℕ) : Function.Periodic (ModularForm.heckeT k p f ∘ UpperHalfPlane.ofComplex) 1 := by
  revert f hf k p
  exact @_root_.P2MW.S_ModularForm_periodic_heckeT_comp_ofComplex.solution
