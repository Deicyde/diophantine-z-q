/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_RegularProlongation_forall_exists_residue_eq_algebraMap_of_mem_residueSpan_inf (git blob ffe64342faa1a52d611f1173620aba0b4a4dd499, sha256 8c4f81b8d8fd60ce1e70b89f9c8da5146a825e740ff13cf2a47b2f7969a8bff3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularProlongation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_RegularProlongation_forall_exists_residue_eq_algebraMap_of_mem_residueSpan_inf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.forall_exists_residue_eq_algebraMap_of_mem_residueSpan_inf
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (h : ∀ i, Fb i)
    (hT : h ∈ Submodule.span (IsLocalRing.ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
          ∀ i, (R i).residue ⟨u, hu i⟩ = h i})
    (hT' : h ∈ Submodule.span (IsLocalRing.ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V → u ∈ V) ∧
          ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) :
    ∀ i, ∃ c : IsLocalRing.ResidueField A, h i = algebraMap (IsLocalRing.ResidueField A) (Fb i) c := by
  revert L A F ι Fb R hR f hf htrL hfd htr heq h hT hT'
  exact @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_forall_exists_residue_eq_algebraMap_of_mem_residueSpan_inf.solution
