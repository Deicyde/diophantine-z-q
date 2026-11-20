/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun (git blob 87e9713aad06a60774a8ee92943c8ce68ff7f81f, sha256 dd466bd5be5dfc196f9f18b95f9f357b075c750f7af3f0eed017e2d416a2d5f8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_SiegelFunction
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.SiegelUnit.exists_isIntegral_hasSum_siegelFun (N : ℕ) (r s : ℤ)
    (hr : 0 ≤ r) (hrN : r < N) (hs : r = 0 → ¬ (N : ℤ) ∣ s) :
    ∃ c : ℕ → ℂ, (∀ n : ℕ, IsIntegral ℤ (c n)) ∧
      c 0 = (if r = 0 then 1 - Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) / (N : ℂ)) else 1) ∧
      IsIntegral ℤ ((N : ℂ) * (c 0)⁻¹) ∧
      (∀ τ : UpperHalfPlane,
        HasSum
          (fun n : ℕ => c n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ) / (N : ℂ)))
          (siegelFun N r s (τ : ℂ) /
            (-Complex.exp (Real.pi * Complex.I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
              Complex.exp (2 * Real.pi * Complex.I *
                (6 * (r : ℂ) ^ 2 - 6 * (r : ℂ) * (N : ℂ) + (N : ℂ) ^ 2) * (τ : ℂ) /
                  (12 * (N : ℂ) ^ 2))))) ∧
      Filter.Tendsto
        (fun τ : UpperHalfPlane => siegelFun N r s (τ : ℂ) /
            (-Complex.exp (Real.pi * Complex.I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
              Complex.exp (2 * Real.pi * Complex.I *
                (6 * (r : ℂ) ^ 2 - 6 * (r : ℂ) * (N : ℂ) + (N : ℂ) ^ 2) * (τ : ℂ) /
                  (12 * (N : ℂ) ^ 2))))
        UpperHalfPlane.atImInfty (nhds (c 0)) := by
  revert N r s hr hrN hs
  exact @_root_.P2MW.S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun.solution
