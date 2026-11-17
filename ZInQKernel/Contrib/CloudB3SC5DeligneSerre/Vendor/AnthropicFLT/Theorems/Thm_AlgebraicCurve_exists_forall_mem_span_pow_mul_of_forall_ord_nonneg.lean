/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_exists_forall_mem_span_pow_mul_of_forall_ord_nonneg (git blob 7c2e90fc06abbf85e043e576e79e5ac46ed48fb0, sha256 b652b2a3fdfd5bff99abc9c395dca93b1f511b3bc13eb46eff150252123b8bf6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_exists_forall_mem_span_pow_mul_of_forall_ord_nonneg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.exists_forall_mem_span_pow_mul_of_forall_ord_nonneg
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    ∃ M₁ : ℕ, ∀ h : F, (∀ v : Place K F, 0 ≤ v.ord x → 0 ≤ v.ord h) →
      h ∈ Submodule.span K {g : F | ∃ j : ℕ, ∃ y ∈ LSpace (M₁ • D), g = x ^ j * y} := by
  revert K F x hx D hD
  exact @_root_.P2MW.S_AlgebraicCurve_exists_forall_mem_span_pow_mul_of_forall_ord_nonneg.solution
