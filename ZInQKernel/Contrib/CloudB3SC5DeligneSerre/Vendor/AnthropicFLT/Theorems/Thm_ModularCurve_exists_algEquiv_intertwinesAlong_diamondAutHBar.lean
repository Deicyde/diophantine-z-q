/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutHBar (git blob d2a388f61d86b76d4171960b3b9d95239fd785df, sha256 53ed4f0a454df92f175b66e1a67c034ee0421fb13254d155101db7acd92ade8e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutHBar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem ModularCurve.exists_algEquiv_intertwinesAlong_diamondAutHBar (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] (d : (ZMod M)ˣ) :
    ∃ τ : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))
        ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)),
      AlgebraicCurve.SemilinearAut.IntertwinesAlong
          (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ).toRingHom
          (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutHBar M H d))
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ) ∧
        AlgebraicCurve.SemilinearAut.IntertwinesAlong
          (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ).toRingHom
          (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutHBar M H d))
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ) := by
  revert M H ℓ d
  exact @_root_.P2MW.S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutHBar.solution
