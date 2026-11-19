/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow (git blob 7d9dc485269c9f59e25a59b02c4e13115cd21048, sha256 8ffa7b3d86dfddeabe553b49d25b4b1b4f443497cf4dc18c21669ca6491059c3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_SiegelFunction
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow (N : ℕ) [NeZero N]
    (e : ZMod N → ZMod N → ℕ) (he : e 0 0 = 0) :
    ∃ (C : ℂ) (d : ℕ → ℂ), C ^ N = 1 ∧ (∀ n : ℕ, IsIntegral ℤ (d n)) ∧
      d 0 = ∏ s : ZMod N,
        (1 - Complex.exp (2 * Real.pi * Complex.I * (s.val : ℂ) / (N : ℂ))) ^ (12 * N * e 0 s) ∧
      d 0 ≠ 0 ∧
      IsIntegral ℤ ((N : ℂ) ^ (12 * N * ∑ r : ZMod N, ∑ s : ZMod N, e r s) * (d 0)⁻¹) ∧
      (∀ τ : UpperHalfPlane,
        HasSum
          (fun n : ℕ => d n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ) / (N : ℂ)))
          ((∏ r : ZMod N, ∏ s : ZMod N,
              siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * e r s)) /
            (C * Complex.exp (2 * Real.pi * Complex.I *
              ((∑ r : ZMod N, ∑ s : ZMod N,
                  (e r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)) : ℂ) * (τ : ℂ) / (N : ℂ))))) ∧
      Filter.Tendsto
        (fun τ : UpperHalfPlane =>
          (∏ r : ZMod N, ∏ s : ZMod N,
              siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * e r s)) /
            (C * Complex.exp (2 * Real.pi * Complex.I *
              ((∑ r : ZMod N, ∑ s : ZMod N,
                  (e r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)) : ℂ) * (τ : ℂ) / (N : ℂ))))
        UpperHalfPlane.atImInfty (nhds (d 0)) := by
  revert N e he
  exact @_root_.P2MW.S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow.solution
