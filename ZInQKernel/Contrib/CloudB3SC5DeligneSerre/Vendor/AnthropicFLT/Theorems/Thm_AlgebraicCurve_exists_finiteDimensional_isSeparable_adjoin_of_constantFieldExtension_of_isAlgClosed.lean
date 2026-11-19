/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_isAlgClosed (git blob 8c8d33f4a5a9b5f720c0680971b4bbcf3c440e4e, sha256 9d1a518546b5107973f804ad922055fa75261c681d6da6e973c635c6bec839da).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_isAlgClosed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem AlgebraicCurve.exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_isAlgClosed
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤) :
    ∃ t' : F', FiniteDimensional (IntermediateField.adjoin K' ({t'} : Set F')) F' ∧
      Algebra.IsSeparable (IntermediateField.adjoin K' ({t'} : Set F')) F' := by
  revert K F K' F' hfg hfg' hgen
  exact @_root_.P2MW.S_AlgebraicCurve_exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_isAlgClosed.solution
