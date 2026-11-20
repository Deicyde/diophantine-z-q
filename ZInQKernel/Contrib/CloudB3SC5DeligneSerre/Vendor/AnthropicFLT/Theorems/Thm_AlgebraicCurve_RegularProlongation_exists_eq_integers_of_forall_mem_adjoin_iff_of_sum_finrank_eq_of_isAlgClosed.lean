/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed (git blob 5f76665e92be99326b65bf73205875772018676f, sha256 fc49e357629fc65179407521f84d3349ea46b9474bb0666fc4eca349baa8a4c3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularProlongation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] [Nonempty ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (i₀ : ι) (V : ValuationSubring F)
    (hV : ∀ e : F, e ∈ IntermediateField.adjoin L {f} → (e ∈ V ↔ e ∈ (R i₀).integers)) :
    ∃ j, V = (R j).integers := by
  revert L A F ι Fb R hR f hf htr heq i₀ V hV
  exact @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed.solution
