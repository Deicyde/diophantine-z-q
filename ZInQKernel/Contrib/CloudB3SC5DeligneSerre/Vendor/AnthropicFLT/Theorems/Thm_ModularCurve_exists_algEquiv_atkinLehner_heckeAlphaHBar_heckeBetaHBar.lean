/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar (git blob 6540f942654a704942acf3c4ada4b8e6b5ec4be1, sha256 b812031e8c4c3f3fb585402814e1ee33b08f2499eb537644c32db2cb8f608113).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H) :
    ∃ w : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)),
      (∀ x : ModularCurve.xHFunctionFieldBar M H,
          w (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ x) =
            ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ x) ∧
      (∀ x : ModularCurve.xHFunctionFieldBar M H,
          w (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ x) =
            ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ
              (ModularCurve.diamondAutHBar M H
                (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM)) x)) := by
  revert M H ℓ hℓM hin
  exact @_root_.P2MW.S_ModularCurve_exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar.solution
