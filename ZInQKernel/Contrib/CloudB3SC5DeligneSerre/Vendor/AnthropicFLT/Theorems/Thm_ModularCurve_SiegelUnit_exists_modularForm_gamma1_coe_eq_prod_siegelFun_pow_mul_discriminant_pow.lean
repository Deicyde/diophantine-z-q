/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_SiegelUnit_exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow (git blob 6d3e611aa0cc34668b3da25bc434e37d5fba7611, sha256 3b433621cb60adb72881bac8f383336964bb693d26e939dea3b0bfb9746583cf).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_SiegelFunction
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.SiegelUnit.exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
    (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (hm0 : m 0 0 = 0)
    (hm : ∀ r s : ZMod N, m r (s + r) = m r s) (t : ℕ)
    (ht : ∀ β : SL(2, ℤ),
      0 ≤ (∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
          (6 * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) ^ 2
            - 6 * (N : ℤ) * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) + (N : ℤ) ^ 2)) + (N : ℤ) * t) :
    ∃ ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (12 * (t : ℤ)),
      (∀ τ : UpperHalfPlane, ϑ τ =
        (∏ r : ZMod N, ∏ s : ZMod N,
          ModularCurve.siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)) *
          ModularForm.discriminant τ ^ t) ∧
      ∀ β : SL(2, ℤ),
        ((⇑ϑ : UpperHalfPlane → ℂ) ∣[12 * (t : ℤ)] (β : GL (Fin 2) ℝ)) =O[UpperHalfPlane.atImInfty]
          fun τ : UpperHalfPlane =>
            Real.exp (-(2 * Real.pi *
              ((((∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
                (6 * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) ^ 2
                  - 6 * (N : ℤ) * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) + (N : ℤ) ^ 2)) : ℤ) : ℝ) / (N : ℝ) + (t : ℝ))) * τ.im) := by
  revert N m hm0 hm t ht
  exact @_root_.P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.solution
