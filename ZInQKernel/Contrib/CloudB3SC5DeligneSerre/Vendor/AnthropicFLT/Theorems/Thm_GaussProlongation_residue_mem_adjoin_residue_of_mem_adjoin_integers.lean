/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_GaussProlongation_residue_mem_adjoin_residue_of_mem_adjoin_integers (git blob 8c3658dbcf157cf29caf668625ca6f295b04f707, sha256 3c8d699b52c2d3c6e965278f91e3a073a2e240f3bb486bd37cdd242a6d7846d4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularProlongation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_GaussProlongation_residue_mem_adjoin_residue_of_mem_adjoin_integers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve

theorem GaussProlongation.residue_mem_adjoin_residue_of_mem_adjoin_integers
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (i₀ i : ι) (w : IntermediateField.adjoin L ({f} : Set F)) (hw : (w : F) ∈ (R i₀).integers)
    (hwi : (w : F) ∈ (R i).integers) :
    (R i).residue ⟨(w : F), hwi⟩ ∈
      IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)) := by
  revert L A F ι Fb R f hf htr i₀ i w hw hwi
  exact @_root_.P2MW.S_GaussProlongation_residue_mem_adjoin_residue_of_mem_adjoin_integers.solution
