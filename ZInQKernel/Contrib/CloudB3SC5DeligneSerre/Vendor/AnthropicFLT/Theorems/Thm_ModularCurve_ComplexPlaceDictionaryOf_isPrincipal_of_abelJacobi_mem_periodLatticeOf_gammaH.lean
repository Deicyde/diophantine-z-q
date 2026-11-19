/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH (git blob a0b81bf73c7fa976091c9017d753afd140bda647, sha256 2d221f9de1b354f32df6292a75292d5918e88684f2b70f45a4d2fe9f402b47c0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.ComplexPlaceDictionaryOf.isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0)
    (hΛ : (c.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) ∈
      ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :
    AlgebraicCurve.Divisor.IsPrincipal (Finsupp.mapDomain D.pt c) := by
  revert M H D c hdeg hΛ
  exact @_root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH.solution
