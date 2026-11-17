/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN (git blob 1398543e5af96406f0df9a53f574754f567bdae7, sha256 e30f61db1c41ecfdf146ade48039d524c4c6dac4a9e57c185c76ada228838a3d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LevelNFunctionField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ)
    (ι : AlgebraicClosure ℚ →+* ℂ)
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring M) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring M) K]
    [IsFractionRing (ModularCurve.LevelN.ring M) K] :
    ∃ Φ : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ Γ) →+* K,
      (∀ c : AlgebraicClosure ℚ,
          Φ (algebraMap (AlgebraicClosure ℚ)
            (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.qExpFunctionFieldC ℚ Γ)) c) =
            algebraMap ℂ K (ι c)) ∧
      (∀ y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ),
          (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ) →
          Φ y = algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)) ∧
      ∀ γ ∈ Γ, ∀ (hst : ∀ G ∈ ModularCurve.LevelN.ring M,
          (fun τ : UpperHalfPlane => G (γ⁻¹ • τ)) ∈ ModularCurve.LevelN.ring M)
        (φ : K ≃ₐ[ℂ] K),
        (∀ (G : UpperHalfPlane → ℂ) (hG : G ∈ ModularCurve.LevelN.ring M),
            φ (algebraMap (ModularCurve.LevelN.ring M) K ⟨G, hG⟩) =
              algebraMap (ModularCurve.LevelN.ring M) K
                ⟨fun τ : UpperHalfPlane => G (γ⁻¹ • τ), hst G hG⟩) →
        ∀ u, φ (Φ u) = Φ u := by
  revert M Γ hΓ hT ι K
  exact @_root_.P2MW.S_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN.solution
