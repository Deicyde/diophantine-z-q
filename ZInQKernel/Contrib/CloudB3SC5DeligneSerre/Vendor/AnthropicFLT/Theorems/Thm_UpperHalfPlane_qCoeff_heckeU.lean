/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_UpperHalfPlane_qCoeff_heckeU (git blob 9bb43ffcacafcea4b48cb053f484b8bac03b2306, sha256 a49351bca04ea3f3bf7d8b977742299fdcbc8235d3ba5ab683d46ee477b74bbb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_UpperHalfPlane_qCoeff_heckeU

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem UpperHalfPlane.qCoeff_heckeU {f : UpperHalfPlane → ℂ} (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) (k : ℤ) {p : ℕ} (hp : p ≠ 0) (n : ℕ) : ModularFormClass.qCoeff (ModularForm.heckeU k p f) n = ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n := by
  revert f hper hhol hbdd k p hp n
  exact @_root_.P2MW.S_UpperHalfPlane_qCoeff_heckeU.solution
