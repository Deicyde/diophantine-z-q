/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC (git blob 4955c606d6e029fe008a2135acefd849321bfaaf, sha256 774454576a9d743a43f387fa4cb715e563f17c88da6a559084f1cf962e12b333).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open AlgebraicCurve open ModularCurve hiding place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC
open scoped MatrixGroups

theorem ModularCurve.inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC
    {L : Type*} [Field L] [Algebra ℚ L] [IsAlgClosed L]
    {F : Type*} [Field F] [Algebra L F]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (φ : F →ₐ[L] ↥(ModularCurve.laurentBaseChange L F₀))
    (hφ : φ.toRingHom.IsIntegral)
    (W : AlgebraicCurve.Place L ↥(ModularCurve.laurentBaseChange L F₀)) :
    W.inertiaDegAlong φ hφ = 1 := by
  revert L F Γ hT F₀ hF φ hφ W
  exact @_root_.P2MW.S_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC.solution
