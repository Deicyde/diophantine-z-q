/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspFormClass_isZeroAt_slash_ratCast (git blob 367ebd1455ec0dd867ae0124845f8aea4be4d579, sha256 567f1ff5c25e11bae3a9a2db4b4c7ea0d9239ca60cb162ed5e0565469cf8125e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspFormClass_isZeroAt_slash_ratCast

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem CuspFormClass.isZeroAt_slash_ratCast {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} [CuspFormClass F Γ k] (f : F) (g : Matrix.GeneralLinearGroup (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c Γ) : OnePoint.IsZeroAt c (SlashAction.map k (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g) ⇑f) k := by
  revert F Γ k f g c hc
  exact @_root_.P2MW.S_CuspFormClass_isZeroAt_slash_ratCast.solution
