/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul (git blob c3d279d19d6c2c21d7d4d277bce4b0f61ad752cc, sha256 350ada6ea123915456540c329bb8e286a649e59530e3e6eaedcb15491ec40dec).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul (M : ℕ)
    [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hin : ∀ d : (ZMod M)ˣ, ∃ σ : ModularCurve.xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ]
      ModularCurve.xHFunctionFieldBar M H, ModularCurve.IsDiamondAutHBar M H d σ)
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    ∃ w : ModularCurve.xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.xHFunctionFieldBar M H,
      (∀ (x : ModularCurve.xHFunctionFieldBar M H) (k : ℤ)
          (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k),
          ModularCurve.coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) *
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) =
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) →
          ModularCurve.coeffMap ι ((w x : ModularCurve.xHFunctionFieldBar M H) :
                LaurentSeries (AlgebraicClosure ℚ)) *
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] W)) =
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] W))) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
          (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
          ∀ x : ModularCurve.xHFunctionFieldBar M H,
            w (ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField M H) σ • x) =
              ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField M H) σ •
                ModularCurve.diamondAutHBar M H (ZMod.unitOfCoprime c hc) (w x)) := by
  revert M H hin ι W hW
  exact @_root_.P2MW.S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul.solution
