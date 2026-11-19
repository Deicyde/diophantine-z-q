/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_SiegelUnit_prod_siegelFun_pow_specialLinearGroup_smul (git blob e754e4fc8bcb63d1dca6cd9bc4e4ce31a0b135db, sha256 4ee17752658fc73c84574f6855e380c4d408d9ffc4a0f60f801ea50384588fba).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_SiegelFunction
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_SiegelUnit_prod_siegelFun_pow_specialLinearGroup_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve

set_option autoImplicit false

open _root_.ModularCurve hiding siegelFun_specialLinearGroup_smul
open scoped MatrixGroups in

theorem ModularCurve.SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul (N : ℕ) [NeZero N]
    (e : ZMod N → ZMod N → ℕ) :
    (∀ (β : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane),
      (∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N (r.val : ℤ) (s.val : ℤ) ((β • τ : UpperHalfPlane) : ℂ) ^ (12 * N * e r s)) =
        ∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N
              ((((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
                  (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N).val : ℤ)
              ((((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
                  (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N).val : ℤ)
              (τ : ℂ) ^ (12 * N * e r s)) ∧
    ((∀ r s : ZMod N, e r (s + r) = e r s) →
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ CongruenceSubgroup.Gamma1 N →
        ∀ τ : UpperHalfPlane,
          (∏ r : ZMod N, ∏ s : ZMod N,
              siegelFun N (r.val : ℤ) (s.val : ℤ) ((γ • τ : UpperHalfPlane) : ℂ) ^ (12 * N * e r s)) =
            ∏ r : ZMod N, ∏ s : ZMod N,
              siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * e r s)) := by
  revert N e
  exact @_root_.P2MW.S_ModularCurve_SiegelUnit_prod_siegelFun_pow_specialLinearGroup_smul.solution
