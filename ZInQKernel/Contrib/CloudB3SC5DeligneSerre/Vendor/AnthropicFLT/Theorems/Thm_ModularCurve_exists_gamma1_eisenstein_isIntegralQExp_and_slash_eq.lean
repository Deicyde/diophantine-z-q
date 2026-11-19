/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq (git blob b8ac33d48387c66937ea48b930fc973236d0e0ea, sha256 c46435a59a9ab692f7c959bbfba00b079737f880b48490d21e042b84356ae0b0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq (M : ℕ) [NeZero M]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ G : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k,
      (∀ c : ZMod M, c ≠ 0 →
        ModularCurve.IsIntegralQExp (G c)
          (PowerSeries.mk fun n : ℕ =>
            (∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = c, (m : ℤ) ^ (k - 1)) +
              (-1) ^ k * ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = -c, (m : ℤ) ^ (k - 1))) ∧
      ∀ (c : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        ((⇑(G c) : UpperHalfPlane → ℂ) ∣[(k : ℤ)] γ) =
          (⇑(G (c * ((γ 0 0 : ℤ) : ZMod M))) : UpperHalfPlane → ℂ) := by
  revert M k hk
  exact @_root_.P2MW.S_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq.solution
