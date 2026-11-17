/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_qExpand_norm_heckeBetaHBar (git blob 1797b1c92c8994ab5a36b4a53e932225d31cc7ec, sha256 aaeab561ff6bd9b1328b377432cb6edb77fa074ea9c4c28b94a7cc2bd4642b9b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_qExpand_norm_heckeBetaHBar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.qExpand_norm_heckeBetaHBar (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (ζ : (AlgebraicClosure ℚ)ˣ) (hζ : IsPrimitiveRoot ζ ℓ)
    (u : ModularCurve.xHFunctionFieldBar M H) :
    ModularCurve.qExpand (AlgebraicClosure ℚ) ℓ
        ((letI := AlgebraicCurve.algebraAlong (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ)
          Algebra.norm (ModularCurve.xHFunctionFieldBar M H)
            (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ u) :
            ModularCurve.xHFunctionFieldBar M H) : LaurentSeries (AlgebraicClosure ℚ)) =
      (∏ b ∈ Finset.range ℓ,
          ModularCurve.qTwist (ζ ^ b)
            ((ModularCurve.diamondAutHBar M H
                (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM)) u :
              ModularCurve.xHFunctionFieldBar M H) : LaurentSeries (AlgebraicClosure ℚ))) *
        ModularCurve.qExpand (AlgebraicClosure ℚ) ℓ
          (ModularCurve.qExpand (AlgebraicClosure ℚ) ℓ (u : LaurentSeries (AlgebraicClosure ℚ))) := by
  revert M H ℓ hℓM hin ζ hζ u
  exact @_root_.P2MW.S_ModularCurve_qExpand_norm_heckeBetaHBar.solution
