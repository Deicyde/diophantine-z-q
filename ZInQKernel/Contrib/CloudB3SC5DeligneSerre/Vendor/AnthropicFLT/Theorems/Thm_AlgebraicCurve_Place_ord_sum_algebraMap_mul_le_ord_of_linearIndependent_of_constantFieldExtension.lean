/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension (git blob 1c34901fede569a948ef21c067e19de09ec9ded2, sha256 860c82dd9e15c6e6c2b5f2baf8d622cc6eafa4971a6af741eb59a7cee162301a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.Place.ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (lift : Place K F → Place K' F')
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (v : Place K F) {ι : Type*} (B : ι → K') (hB : LinearIndependent K B)
    (g : ι →₀ F) (hg : g ≠ 0) :
    (∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j)) ≠ 0 ∧
    ∀ j ∈ g.support,
      (lift v).ord (∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j)) ≤
        v.ord (g j) := by
  revert K F K' F' hfg hfg' hgen lift hlift_ord v ι B hB g hg
  exact @_root_.P2MW.S_AlgebraicCurve_Place_ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension.solution
