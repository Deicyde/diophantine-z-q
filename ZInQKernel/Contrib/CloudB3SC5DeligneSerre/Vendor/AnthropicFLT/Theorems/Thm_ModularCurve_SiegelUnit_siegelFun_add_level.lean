/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_SiegelUnit_siegelFun_add_level (git blob f222aa34dbfad81435704b1df43d1aa119d84570, sha256 9d128371d5dd65aad07c65e3a5c99d6393932d8f2349d32ce546e474c7411242).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_SiegelFunction
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_SiegelUnit_siegelFun_add_level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.SiegelUnit.siegelFun_add_level (N : ℕ) (r s : ℤ) :
    (∀ z : ℂ, siegelFun N r (s + N) z =
        Complex.exp (Real.pi * Complex.I * ((r : ℂ) - (N : ℂ)) / (N : ℂ)) * siegelFun N r s z) ∧
    (∀ τ : UpperHalfPlane, siegelFun N (r + N) s (τ : ℂ) =
        -Complex.exp (-(Real.pi * Complex.I * (s : ℂ) / (N : ℂ))) * siegelFun N r s (τ : ℂ)) := by
  revert N r s
  exact @_root_.P2MW.S_ModularCurve_SiegelUnit_siegelFun_add_level.solution
