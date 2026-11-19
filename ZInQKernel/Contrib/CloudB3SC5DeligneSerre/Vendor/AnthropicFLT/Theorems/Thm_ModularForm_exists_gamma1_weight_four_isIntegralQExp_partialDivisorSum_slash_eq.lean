/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_exists_gamma1_weight_four_isIntegralQExp_partialDivisorSum_slash_eq (git blob 38161ab8a104bb105b68272b384bb99358451918, sha256 d88f9f1954961108f8e13406fc67345473b6c8b0944b5932af2899c9b916ae9b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_exists_gamma1_weight_four_isIntegralQExp_partialDivisorSum_slash_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem ModularForm.exists_gamma1_weight_four_isIntegralQExp_partialDivisorSum_slash_eq
    (M : ℕ) [NeZero M] (hM : 3 ≤ M) :
    ∃ R : (ZMod M)ˣ → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 4,
      (∀ c : (ZMod M)ˣ, ModularCurve.IsIntegralQExp (R c)
        (PowerSeries.mk fun n : ℕ => if n = 0 then 0 else
          ∑ d ∈ n.divisors,
            if ((n / d : ℕ) : ZMod M) = (c : ZMod M) ∨ ((n / d : ℕ) : ZMod M) = -(c : ZMod M)
            then (d : ℤ) ^ 3 else 0)) ∧
      (∀ (c : (ZMod M)ˣ) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M),
        ((⇑(R c) : UpperHalfPlane → ℂ) ∣[(4 : ℤ)] (γ : GL (Fin 2) ℝ)) =
          ⇑(R (c * (CohCarrier.gamma0Units M ⟨γ, hγ⟩)⁻¹))) := by
  revert M hM
  exact @_root_.P2MW.S_ModularForm_exists_gamma1_weight_four_isIntegralQExp_partialDivisorSum_slash_eq.solution
