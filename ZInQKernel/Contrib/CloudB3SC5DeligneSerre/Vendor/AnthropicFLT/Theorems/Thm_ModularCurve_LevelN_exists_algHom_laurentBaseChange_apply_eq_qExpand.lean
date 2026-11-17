/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_LevelN_exists_algHom_laurentBaseChange_apply_eq_qExpand (git blob a96652c268e6782b6b20ea45a9d64f8e62bf1f2b, sha256 6020f460a543f56fac5bf87259a97a411933db8907269f811ed1cb0ba7627647).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LevelNFunctionField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_LevelN_exists_algHom_laurentBaseChange_apply_eq_qExpand

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.LevelN.exists_algHom_laurentBaseChange_apply_eq_qExpand
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
    (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ) :
    ∃ Ψ : ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ) →ₐ[ℂ] K,
      ∀ u : ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ),
        E (Ψ u) = ModularCurve.qExpand ℂ M (u : LaurentSeries ℂ) := by
  revert M K σ hker hfixed E hEj Γ hΓ hT
  exact @_root_.P2MW.S_ModularCurve_LevelN_exists_algHom_laurentBaseChange_apply_eq_qExpand.solution
