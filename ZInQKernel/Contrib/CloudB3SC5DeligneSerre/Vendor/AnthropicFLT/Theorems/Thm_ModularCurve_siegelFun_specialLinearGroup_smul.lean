/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_siegelFun_specialLinearGroup_smul (git blob 1083124c606a2552a7cf6b381c5b7a0ed98b2a2d, sha256 f6e5506eb16064c044be73977cb883106cee678c6f1e290b97c56aacdfca9892).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_SiegelFunction
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_siegelFun_specialLinearGroup_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve
theorem ModularCurve.siegelFun_specialLinearGroup_smul (N : ℕ)
    (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ μ : ℂ, μ ^ 12 = 1 ∧ ∀ (r s : ℤ) (τ : UpperHalfPlane),
      siegelFun N r s ((α • τ : UpperHalfPlane) : ℂ) =
        μ * siegelFun N (r * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + s * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
          (r * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + s * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 1) (τ : ℂ) := by
  revert N α
  exact @_root_.P2MW.S_ModularCurve_siegelFun_specialLinearGroup_smul.solution
