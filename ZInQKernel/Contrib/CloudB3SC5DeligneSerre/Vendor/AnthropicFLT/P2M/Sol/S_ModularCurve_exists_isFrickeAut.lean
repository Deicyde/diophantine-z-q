/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_exists_isFrickeAut (git blob e3b880bfa649dea247941986b681ea3ddb5556c4, sha256 e3f4e6f02613d730c68a756e435db8fa6cacd34b2392f3c8ef30f63411a03f88).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_AtkinLehner
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_isFrickeAut_of_modularPolynomialData
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_phiIrreducible_evalSymm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_exists_isFrickeAut

set_option autoImplicit false

open ModularCurve AlgebraicCurve IntermediateField

noncomputable section

theorem solution (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : ∃ σ : modularFunctionField ℓ ≃ₐ[ℚ] modularFunctionField ℓ, IsFrickeAut ℓ σ := by
  obtain ⟨data, hirr, hsymm⟩ := ModularCurve.exists_phiIrreducible_evalSymm ℓ
  exact ModularCurve.exists_isFrickeAut_of_modularPolynomialData data hsymm hirr

end
