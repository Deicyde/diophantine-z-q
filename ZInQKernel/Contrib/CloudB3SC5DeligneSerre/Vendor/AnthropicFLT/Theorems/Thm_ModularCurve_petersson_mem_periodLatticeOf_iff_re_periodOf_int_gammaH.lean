/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH (git blob 87b8b56d7eb6cbdca5949543f75a5d78ed5d399c, sha256 2d8e4653526bbde4c3dc022933a57672d55acd4a40bc9dbbd520d61750013cc7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology

theorem ModularCurve.petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) 2) :
    (∃ Λ ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H), ∀ g : CuspForm (CohCarrier.GammaH M H) 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))), UpperHalfPlane.petersson 2 ⇑f ⇑g τ) = Λ g) ↔
      ∀ γ : CohCarrier.GammaH M H, ∃ m : ℤ, (ModularCurve.periodOf (CohCarrier.GammaH M H) γ f).re = m := by
  revert M H f
  exact @_root_.P2MW.S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH.solution
