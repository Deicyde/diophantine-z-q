/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_of_forall_mem_adjoin_iff_of_isAlgebraic (git blob cb41ef462255ff21f636cd6a73d1e749612e3c1c, sha256 0120cfae9b0164a5fe2b9f7cf7d2fce25451dce5a6703f12fef9e66c8cb12dcf).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularProlongation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_of_forall_mem_adjoin_iff_of_isAlgebraic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_of_forall_mem_adjoin_iff_of_isAlgebraic
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (f : F) (hfO : f ∈ R.integers)
    (htr : Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfO⟩))
    [Algebra.IsAlgebraic (IntermediateField.adjoin L ({f} : Set F)) F]
    (W : ValuationSubring F)
    (hW : ∀ e : F, e ∈ IntermediateField.adjoin L ({f} : Set F) → (e ∈ W ↔ e ∈ R.integers)) :
    ∃ (_ : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField W))
      (R' : RegularProlongation A F (IsLocalRing.ResidueField W)),
      R'.integers = W ∧ ∃ hf' : f ∈ R'.integers,
        Transcendental (IsLocalRing.ResidueField A) (R'.residue ⟨f, hf'⟩) := by
  revert L A F Fbar R f hfO htr W hW
  exact @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_of_forall_mem_adjoin_iff_of_isAlgebraic.solution
