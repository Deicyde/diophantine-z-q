/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_LevelN_valuation_apply_smul_le_one_of_tendsto_div_smul (git blob 76562d19acca09a49cc8ee38283f681623e126e8, sha256 4e68f63250d916ac25d0105f39709ed3df3476a667a5fdec678036aa3b43ffd5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LevelNFunctionField
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_LevelN_valuation_apply_smul_le_one_of_tendsto_div_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.LevelN.valuation_apply_smul_le_one_of_tendsto_div_smul
    (M : ℕ) [NeZero M]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring M) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring M) K]
    [IsFractionRing (ModularCurve.LevelN.ring M) K]
    (hst : ∀ γ : SL(2, ℤ), ∀ F ∈ ModularCurve.LevelN.ring M,
      (fun τ : UpperHalfPlane => F (γ • τ)) ∈ ModularCurve.LevelN.ring M)
    (σ : SL(2, ℤ) →* (K ≃ₐ[ℂ] K))
    (hσ : ∀ (γ : SL(2, ℤ)) (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring M),
      σ γ (algebraMap (ModularCurve.LevelN.ring M) K ⟨F, hF⟩) =
        algebraMap (ModularCurve.LevelN.ring M) K
          ⟨fun τ : UpperHalfPlane => F (γ⁻¹ • τ), hst γ⁻¹ F hF⟩)
    (E : K →ₐ[ℂ] LaurentSeries ℂ)
    (hEj : E (algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)) =
      ModularCurve.qExpand ℂ M (ModularCurve.jqModC ℂ))
    (hEq : ∀ (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring M) (m : ℕ),
      UpperHalfPlane.IsBoundedAtImInfty (F * ModularForm.discriminant ^ m) →
        E (algebraMap (ModularCurve.LevelN.ring M) K ⟨F, hF⟩) *
            HahnSeries.ofPowerSeries ℤ ℂ
              (UpperHalfPlane.qExpansion M (ModularForm.discriminant : UpperHalfPlane → ℂ)) ^ m =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion M (F * ModularForm.discriminant ^ m)))
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ)
    {k : ℤ} (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0) (z : K)
    (hz : E z * ModularCurve.qExpand ℂ M
        ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ModularCurve.qExpand ℂ M
        ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (γ : SL(2, ℤ)) (L : ℂ) (hL : L ≠ 0)
    (hlim : Filter.Tendsto
      (fun τ : UpperHalfPlane => (g : UpperHalfPlane → ℂ) (γ⁻¹ • τ) / (h : UpperHalfPlane → ℂ) (γ⁻¹ • τ))
      atImInfty (𝓝 L)) :
    Valued.v (E (σ γ z)) ≤ 1 := by
  revert M K hst σ hσ E hEj hEq Γ hΓ hT k g h hh z hz γ L hL hlim
  exact @_root_.P2MW.S_ModularCurve_LevelN_valuation_apply_smul_le_one_of_tendsto_div_smul.solution
