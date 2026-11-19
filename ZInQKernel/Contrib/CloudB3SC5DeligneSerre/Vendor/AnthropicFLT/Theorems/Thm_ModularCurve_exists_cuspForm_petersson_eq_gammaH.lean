/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_cuspForm_petersson_eq_gammaH (git blob 90dacf9be32f8d93bc6218319b4c0e4469802ac3, sha256 4b8b881d794dd5c1d9719b3dc4179afdb296b50bf95a014f17945f69b99fcbe5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_cuspForm_petersson_eq_gammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups

theorem ModularCurve.exists_cuspForm_petersson_eq_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (ℓ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)) :
    ∃ f : CuspForm (CohCarrier.GammaH M H) 2,
      ∀ g : CuspForm (CohCarrier.GammaH M H) 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))), UpperHalfPlane.petersson 2 ⇑f ⇑g τ) = ℓ g := by
  revert M H ℓ
  exact @_root_.P2MW.S_ModularCurve_exists_cuspForm_petersson_eq_gammaH.solution
