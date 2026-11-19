/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one (git blob 1f53aaf8a64201a2043087f6bfb007f47de7a26d, sha256 80eb3ce460e1314fe0fa0ca15af207ef0c0b116fbd56f1fcb860d24297c502bd).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularProlongation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    [Ring.KrullDimLE 1 A]
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
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∑ i, genusFF (IsLocalRing.ResidueField A) (Fb i) ≤ genusFF L F := by
  revert L A F ι Fb R hR f hf htrL hfd htr heq
  exact @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one.solution
