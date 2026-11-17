/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_modularFunctionFieldBar_eq_restrictScalars (git blob 54908735e0b558a46754857f7e369a03deaebfc6, sha256 afde41cabb3b10c22241f758a3c51f508d8be3fa74149807d95fbe3b7b1f863e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_AtkinLehner
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_modularFunctionFieldBar_eq_restrictScalars

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve AlgebraicCurve

theorem ModularCurve.modularFunctionFieldBar_eq_restrictScalars (ℓ : ℕ) [Fact ℓ.Prime] : modularFunctionFieldBar ℓ = (IntermediateField.adjoin (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jqModC (AlgebraicClosure ℚ)} : Set (LaurentSeries (AlgebraicClosure ℚ)))) ({jqNModC (AlgebraicClosure ℚ) ℓ} : Set (LaurentSeries (AlgebraicClosure ℚ)))).restrictScalars (AlgebraicClosure ℚ) := by
  revert ℓ
  exact @_root_.P2MW.S_ModularCurve_modularFunctionFieldBar_eq_restrictScalars.solution
