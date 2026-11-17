/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlacesOf
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u
theorem AlgebraicCurve.placesOf_union_eq_univ_of_sup_eq_top {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U V : C.Opens) (hUV : U ⊔ V = ⊤) (hU : U ≠ ⊤) (hV : V ≠ ⊤) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    AlgebraicCurve.placesOf c U ∪ AlgebraicCurve.placesOf c V = Set.univ ∧
      (∃ v : AlgebraicCurve.Place K C.functionField, v ∉ AlgebraicCurve.placesOf c U) ∧
      (∃ v : AlgebraicCurve.Place K C.functionField, v ∉ AlgebraicCurve.placesOf c V) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top.solution
