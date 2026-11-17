/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed (git blob 3ead05300d2177ce9b941b3f76ffb23387cd79b6, sha256 4e5db404201ed414ab5e1365bdde37b2f37a7a31dea60d0ed54c816996cfc9f0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_sum_support
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_poleDivisor_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    ∃ S : Finset (Place k F), (∀ P, P ∈ S ↔ P.ord x < 0) ∧
      ∑ P ∈ S, (-P.ord x) = (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by
  classical
  haveI := hfin
  haveI : IsCurveOver k F := isCurveOver_of_isAlgClosed_of_transcendental x hx
  obtain ⟨D, hD⟩ := AlgebraicCurve.exists_poleDivisor_of_transcendental x hx
  refine ⟨D.support, fun P => ?_, ?_⟩
  · rw [Finsupp.mem_support_iff, hD P]
    constructor
    · intro h; by_contra h'; exact h (max_eq_left (by omega))
    · intro h; rw [max_eq_right (by omega)]; omega
  · have hdeg := AlgebraicCurve.degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental x hx D hD
    rw [AlgebraicCurve.Divisor.degree_eq_sum_support] at hdeg
    rw [← hdeg]
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [IsCurveOver.deg_eq_one_of_isAlgClosed P, Nat.cast_one, mul_one, hD P]
    rw [Finsupp.mem_support_iff, hD P] at hP
    have : P.ord x < 0 := by by_contra h'; exact hP (max_eq_left (by omega))
    rw [max_eq_right (by omega)]
