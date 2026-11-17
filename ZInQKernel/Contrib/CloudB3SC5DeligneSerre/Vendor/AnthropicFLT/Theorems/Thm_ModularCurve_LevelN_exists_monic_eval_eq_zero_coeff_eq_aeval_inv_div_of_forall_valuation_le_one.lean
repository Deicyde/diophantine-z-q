/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_LevelN_exists_monic_eval_eq_zero_coeff_eq_aeval_inv_div_of_forall_valuation_le_one (git blob 3735c845a3739b1bb050db8a9be03837117c5fa3, sha256 b7697a8172afe5adb3f0fb89b5a8b6aa9bbca509bb058e757c08f3470287f1bb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LevelNFunctionField
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_LevelN_exists_monic_eval_eq_zero_coeff_eq_aeval_inv_div_of_forall_valuation_le_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open Polynomial
open scoped MatrixGroups

theorem ModularCurve.LevelN.exists_monic_eval_eq_zero_coeff_eq_aeval_inv_div_of_forall_valuation_le_one
    (M : ℕ) [NeZero M]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring M) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring M) K]
    [IsFractionRing (ModularCurve.LevelN.ring M) K]
    (σ : SL(2, ℤ) →* (K ≃ₐ[ℂ] K))
    (hker : σ.ker = CongruenceSubgroup.Gamma M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)))
    (hfixed : IntermediateField.fixedField σ.range =
      IntermediateField.adjoin ℂ
        ({algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)} : Set K))
    (E : K →ₐ[ℂ] LaurentSeries ℂ)
    (hEj : E (algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)) =
      ModularCurve.qExpand ℂ M (ModularCurve.jqModC ℂ))
    (z : K) (hz : ∀ γ : SL(2, ℤ), Valued.v (E (σ γ z)) ≤ 1) :
    ∃ P : K[X], P.Monic ∧ P.eval z = 0 ∧
      ∀ i : ℕ, ∃ p q : ℂ[X], q.coeff 0 ≠ 0 ∧
        P.coeff i =
          aeval (algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M))⁻¹ p /
            aeval (algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M))⁻¹ q := by
  revert M K σ hker hfixed E hEj z hz
  exact @_root_.P2MW.S_ModularCurve_LevelN_exists_monic_eval_eq_zero_coeff_eq_aeval_inv_div_of_forall_valuation_le_one.solution
