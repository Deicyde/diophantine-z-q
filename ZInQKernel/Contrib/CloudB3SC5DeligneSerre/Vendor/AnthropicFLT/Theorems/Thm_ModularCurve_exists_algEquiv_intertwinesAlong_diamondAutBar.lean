/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar (git blob ddd5edf9e5c33264054d38d06a099d411fab47ef, sha256 9d3b80e727874b2560bb93081fa2a8a89cd3552688f3417b485c84eae7f38277).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1Diamond
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.exists_algEquiv_intertwinesAlong_diamondAutBar (M : ℕ) [NeZero M] (ℓ : ℕ)
    [NeZero ℓ] (d : ℕ) :
    ∃ τ : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ))
        ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ)),
      AlgebraicCurve.SemilinearAut.IntertwinesAlong (ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ).toRingHom
          (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar M d))
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ) ∧
        AlgebraicCurve.SemilinearAut.IntertwinesAlong (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ).toRingHom
          (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar M d))
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ) := by
  revert M ℓ d
  exact @_root_.P2MW.S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar.solution
