/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_Period_finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one (git blob b802f2e6c1c65ec54594bf2b470593c3121e9421, sha256 1fec755f7da6dd54700e5b6d448222e1f5f282be11fd7309ace55f2f556970eb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_Period_finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
theorem ModularCurve.Period.finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ) (K : Type) [Field K] :
    Module.finrank K (ModularCurve.Period.parabolicHoms K Γ K)
      + Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
          (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ))
      ≤ Module.finrank K (Additive Γ →+ K) + 1 := by
  revert Γ hneg K
  exact @_root_.P2MW.S_ModularCurve_Period_finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one.solution
