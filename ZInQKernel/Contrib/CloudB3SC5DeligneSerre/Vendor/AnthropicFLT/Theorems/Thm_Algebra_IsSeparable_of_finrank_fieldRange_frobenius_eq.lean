/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Algebra_IsSeparable_of_finrank_fieldRange_frobenius_eq (git blob b73cdc1da8dd171fc702a7e341adadead0724148, sha256 bc2aec7d7933e612f08da99c5391a0462014eed5f529a3bcf4278ddf47f1aba4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.Separable
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_IsSeparable_of_finrank_fieldRange_frobenius_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq {E F : Type*} [Field E] [Field F] [Algebra E F] [FiniteDimensional E F] (p : ℕ) [Fact p.Prime] [CharP F p] (hdeg : Module.finrank (frobenius F p).fieldRange F = p) (y : E) (hy : algebraMap E F y ∉ (frobenius F p).fieldRange) : Algebra.IsSeparable E F := by
  revert E F p hdeg y hy
  exact @_root_.P2MW.S_Algebra_IsSeparable_of_finrank_fieldRange_frobenius_eq.solution
