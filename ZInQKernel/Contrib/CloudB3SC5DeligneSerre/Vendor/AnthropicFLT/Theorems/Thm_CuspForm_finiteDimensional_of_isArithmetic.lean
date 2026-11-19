/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic (git blob 4b638a275f4cfca63607a651baa4a5b084f29f47, sha256 1a333466f7c64dc6676b16f2ea71366a6ebe11b0880aec48ba188f2bf7d0d801).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_finiteDimensional_of_isArithmetic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups
theorem CuspForm.finiteDimensional_of_isArithmetic (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] [𝒢.HasDetOne] (k : ℤ) : FiniteDimensional ℂ (CuspForm 𝒢 k) := by
  revert 𝒢 k
  exact @_root_.P2MW.S_CuspForm_finiteDimensional_of_isArithmetic.solution
