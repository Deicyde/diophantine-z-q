/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Pic0_torsion_move_of_forall_isRational (git blob 635e7a9c5859006bc1a86dbee590d4348ed90729, sha256 7af55253cc017608cbc3c6525855d35c1a5102a807eb8e94b284c8841a2d4cf5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Pic0_torsion_move_of_forall_isRational

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.Pic0.torsion.move_of_forall_isRational {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F] (hrat : ∀ v : Place K F, v.IsRational) (n : ℕ) (x : Pic0.torsion K F n) (S : Finset (Place K F)) :
    ∃ D : Divisor.degZero (K := K) (F := F),
      Pic0.mk D = (x : Pic0 K F) ∧
      (∀ v ∈ (D : Divisor K F).support, Place.IsRational v) ∧
      (∀ v ∈ (D : Divisor K F).support, v ∉ S) := by
  revert K F hrat n x S
  exact @_root_.P2MW.S_AlgebraicCurve_Pic0_torsion_move_of_forall_isRational.solution
