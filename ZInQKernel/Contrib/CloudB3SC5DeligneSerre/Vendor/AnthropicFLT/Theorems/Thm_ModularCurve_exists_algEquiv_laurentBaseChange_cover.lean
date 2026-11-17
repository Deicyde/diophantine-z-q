/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_cover (git blob 9935be1ae1695212a2b664004e53f1311e170942, sha256 f87d1ea6597396125a953eacf34417ccc824d76bf960dde1060d361671a7a6ef).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_algEquiv_laurentBaseChange_cover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.exists_algEquiv_laurentBaseChange_cover
    (L : Type*) [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (σ₀ : ↥F₀ ≃+* ↥F₀) :
    ∃ τ : ↥(ModularCurve.laurentBaseChange L F₀) ≃ₐ[L] ↥(ModularCurve.laurentBaseChange L F₀),
      ∀ y : ↥F₀,
        ((τ ⟨ModularCurve.coeffEmb L (y : LaurentSeries ℚ),
              ModularCurve.coeffEmb_mem_laurentBaseChange L y.2⟩ :
            ↥(ModularCurve.laurentBaseChange L F₀)) : LaurentSeries L)
          = ModularCurve.coeffEmb L ((σ₀ y : ↥F₀) : LaurentSeries ℚ) := by
  revert L F₀ σ₀
  exact @_root_.P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_cover.solution
