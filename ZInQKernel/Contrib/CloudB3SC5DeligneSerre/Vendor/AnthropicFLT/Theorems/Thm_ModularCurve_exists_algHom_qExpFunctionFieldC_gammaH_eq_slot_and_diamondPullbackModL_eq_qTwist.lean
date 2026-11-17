/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_eq_slot_and_diamondPullbackModL_eq_qTwist (git blob f43fd57855de93e5d98578b51648a48abc4dbdf7, sha256 8e18b3e16a4793fb83db4e55d4cf1b07acb28c4c9d0fe3bf1909faeb47e5d4d8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0ModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHDiamondModL
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_eq_slot_and_diamondPullbackModL_eq_qTwist

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped MatrixGroups

theorem ModularCurve.exists_algHom_qExpFunctionFieldC_gammaH_eq_slot_and_diamondPullbackModL_eq_qTwist
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M)
    (ρ : CongruenceSubgroup.Gamma0 M →*
      (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
        ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)))
    (hρ : ModularCurve.IsDiamondPullbackModL K M H ρ)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (a : ℕ) [NeZero a] (b : ℤ)
    (ha : (a : ℤ) ∣ g 1 0) (haM : a ∣ M) (hb : g 1 0 * b ≡ g 1 1 * a [ZMOD M]) :
    ∃ Θ : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] LaurentSeries K,
      (∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H),
        (x : LaurentSeries K) = ModularCurve.jqModC K →
          Θ x = ModularCurve.qExpand K M (ModularCurve.jqModC K)) ∧
      (∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H),
        (x : LaurentSeries K) = ModularCurve.jqNModC K M →
          Θ x = ModularCurve.qExpand K (a * a)
            (ModularCurve.qTwist (ζ ^ (b * (a : ℤ))) (ModularCurve.jqModC K))) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 M) (m : ℤ),
        (g⁻¹ * (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) * g = ModularGroup.T ^ m ∨
          g⁻¹ * (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) * g = -(ModularGroup.T ^ m)) →
        ∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H),
          Θ (ρ γ⁻¹ x) = ModularCurve.qTwist (ζ ^ m) (Θ x)) := by
  revert M H ℓ hℓM K ζ hζ ρ hρ g a b ha haM hb
  exact @_root_.P2MW.S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_eq_slot_and_diamondPullbackModL_eq_qTwist.solution
