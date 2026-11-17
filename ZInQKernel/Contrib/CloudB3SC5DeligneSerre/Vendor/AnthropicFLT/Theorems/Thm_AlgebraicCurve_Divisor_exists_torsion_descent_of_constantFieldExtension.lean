/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension (git blob fe07c2915cd195cbc78754ce8d940e1c99f7881e, sha256 b4f5dcef81fd6551b63b9d2f4bf10a09046db61e537064e5dad1a8073d8a1e67).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.Divisor.exists_torsion_descent_of_constantFieldExtension
    (K F K' F' : Type*) [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (n : ℕ) (hn : n ≠ 0) (D' : Divisor K' F')
    (hD' : ∃ g' : F', g' ≠ 0 ∧ ∀ v' : Place K' F', (n : ℤ) * D' v' = v'.ord g') :
    ∃ (D : Divisor K F) (h' : F'), h' ≠ 0 ∧
      (∃ g : F, g ≠ 0 ∧ ∀ v : Place K F, (n : ℤ) * D v = v.ord g) ∧
      (∀ (v : Place K F) (v' : Place K' F'),
        v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
          D' v' = D v + v'.ord h') ∧
      (∀ v' : Place K' F',
        (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
          D' v' = v'.ord h') := by
  revert K F K' F' hfg hfg' hgen n hn D' hD'
  exact @_root_.P2MW.S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension.solution
