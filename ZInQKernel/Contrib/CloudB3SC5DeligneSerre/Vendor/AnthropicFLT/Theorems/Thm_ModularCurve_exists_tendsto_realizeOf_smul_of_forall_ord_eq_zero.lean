/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero (git blob c7981bbcc11d0a9fcce41087bcc2dd2130739c62, sha256 e148772a183e1e9c1c8ab8cef238239a784ba7dd071e3b9de61c409a38fd71ea).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (x : ModularCurve.laurentBaseChange ℂ F₀) (hx : x ≠ 0)
    (y : ModularCurve.laurentBaseChange ℂ F₀) (hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (hord : ∀ v : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ F₀),
      y ∉ v.toValuationSubring → v.ord x = 0)
    (σ : SL(2, ℤ)) :
    ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto
        (fun τ : UpperHalfPlane => ModularCurve.realizeOf Γ (x : LaurentSeries ℂ) (σ • τ))
        atImInfty (𝓝 L) := by
  revert Γ hT F₀ hF x hx y hy hord σ
  exact @_root_.P2MW.S_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.solution
