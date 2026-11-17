/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_RegularProlongation_mem_adjoin_iff_mem_integers_iff_of_transcendental_residue (git blob 39c0c7150cbfac8774afcae0c51a1458f3560ae6, sha256 522763e88a75dffae7bf681cff1a1d1ea464f2084a31ddee506e2527ed3760d2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularProlongation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_RegularProlongation_mem_adjoin_iff_mem_integers_iff_of_transcendental_residue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.mem_adjoin_iff_mem_integers_iff_of_transcendental_residue
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fb₁ Fb₂ : Type*} [Field Fb₁] [Field Fb₂]
    [Algebra (IsLocalRing.ResidueField A) Fb₁] [Algebra (IsLocalRing.ResidueField A) Fb₂]
    (R₁ : RegularProlongation A F Fb₁) (R₂ : RegularProlongation A F Fb₂)
    (f : F) (hf₁ : f ∈ R₁.integers) (hf₂ : f ∈ R₂.integers)
    (htr₁ : Transcendental (IsLocalRing.ResidueField A) (R₁.residue ⟨f, hf₁⟩))
    (htr₂ : Transcendental (IsLocalRing.ResidueField A) (R₂.residue ⟨f, hf₂⟩))
    (e : F) (he : e ∈ IntermediateField.adjoin L ({f} : Set F)) :
    e ∈ R₁.integers ↔ e ∈ R₂.integers := by
  revert L A F Fb₁ Fb₂ R₁ R₂ f hf₁ hf₂ htr₁ htr₂ e he
  exact @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_mem_adjoin_iff_mem_integers_iff_of_transcendental_residue.solution
