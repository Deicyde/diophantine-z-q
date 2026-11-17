/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed (git blob 1cb45989049ed4c77a063ab5771212dee727f1e9, sha256 53b551c0071d46bd7e576bab661e028b1a2f3a6e14573d3dde5c298b5d9396e4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    ∃ S : Finset (Place k F), (∀ P, P ∈ S ↔ P.ord x < 0) ∧
      ∑ P ∈ S, (-P.ord x) = (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by
  revert k F x hx hfin
  exact @_root_.P2MW.S_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed.solution
