/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Pic0_torsion_move_of_forall_isRational (git blob eeb2c06a4b70c155722606cfd8cd71111242047b, sha256 2963b9772cfcd1f224d09a1ff89952eae9cb88b76f809bd2b9f7ca4582d87882).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Pic0_exists_mk_eq_forall_notMem_support

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Pic0_torsion_move_of_forall_isRational

set_option Elab.async false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F] (hrat : ∀ v : Place K F, v.IsRational) (n : ℕ) (x : Pic0.torsion K F n) (S : Finset (Place K F)) :
    ∃ D : Divisor.degZero (K := K) (F := F),
      Pic0.mk D = (x : Pic0 K F) ∧
      (∀ v ∈ (D : Divisor K F).support, Place.IsRational v) ∧
      (∀ v ∈ (D : Divisor K F).support, v ∉ S) := by
  obtain ⟨D, hD, hS⟩ := Pic0.exists_mk_eq_forall_notMem_support (x : Pic0 K F) S
  exact ⟨D, hD, fun v _ => hrat v, hS⟩

end
