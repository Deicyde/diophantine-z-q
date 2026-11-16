/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicCurve
export AlgebraicCurve (Place baseToFunctionField placesOf placesOf_sup exists_closedPoint_range_stalk_eq isClosed_singleton_of_ne_genericPoint exists_place_range_stalk_eq eq_of_range_stalk_eq)
open AlgebraicCurve
open CategoryTheory AlgebraicGeometry TopologicalSpace

variable {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsIntegral C]

theorem placesOf_top [IsProper c] [SmoothOfRelativeDimension 1 c] :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c (⊤ : C.Opens) = Set.univ := by
  letI := (baseToFunctionField c).toAlgebra
  refine Set.eq_univ_of_forall fun v => ?_
  obtain ⟨x, hx, hv⟩ := exists_closedPoint_range_stalk_eq c v
  exact ⟨x, trivial, hx, hv⟩

theorem exists_not_mem_placesOf [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U V : C.Opens) (hUV : U ⊔ V = ⊤) (hU : U ≠ ⊤) (hV : V ≠ ⊤) :
    letI := (baseToFunctionField c).toAlgebra
    ∃ v : Place K C.functionField, v ∉ placesOf c U := by
  letI := (baseToFunctionField c).toAlgebra

  have hUne : (U : Set C).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hU0 : U = ⊥ := Opens.ext h
    rw [hU0, bot_sup_eq] at hUV
    exact hV hUV
  have hη : genericPoint C ∈ U :=
    ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using hUne)

  obtain ⟨x, hxU⟩ : ∃ x : C, x ∉ U :=
    not_forall.mp fun h => hU (Opens.ext (Set.eq_univ_of_forall h))
  have hxη : x ≠ genericPoint C := fun h => hxU (h ▸ hη)
  have hxcl := isClosed_singleton_of_ne_genericPoint c x hxη
  obtain ⟨v, hv⟩ := exists_place_range_stalk_eq c x hxcl
  refine ⟨v, ?_⟩
  rintro ⟨y, hyU, -, hvy⟩
  have hxy : x = y := eq_of_range_stalk_eq c x y (hv.trans hvy.symm)
  exact hxU (hxy ▸ hyU)

theorem placesOf_union_eq_univ_of_sup_eq_top' [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U V : C.Opens) (hUV : U ⊔ V = ⊤) (hU : U ≠ ⊤) (hV : V ≠ ⊤) :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c U ∪ placesOf c V = Set.univ ∧
      (∃ v : Place K C.functionField, v ∉ placesOf c U) ∧
      (∃ v : Place K C.functionField, v ∉ placesOf c V) := by
  letI := (baseToFunctionField c).toAlgebra
  refine ⟨?_, exists_not_mem_placesOf c U V hUV hU hV,
    exists_not_mem_placesOf c V U (sup_comm U V ▸ hUV) hV hU⟩
  rw [← placesOf_sup, hUV, placesOf_top]

end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top.AlgebraicCurve in
theorem solution {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U V : C.Opens) (hUV : U ⊔ V = ⊤) (hU : U ≠ ⊤) (hV : V ≠ ⊤) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    AlgebraicCurve.placesOf c U ∪ AlgebraicCurve.placesOf c V = Set.univ ∧
      (∃ v : AlgebraicCurve.Place K C.functionField, v ∉ AlgebraicCurve.placesOf c U) ∧
      (∃ v : AlgebraicCurve.Place K C.functionField, v ∉ AlgebraicCurve.placesOf c V) :=
  placesOf_union_eq_univ_of_sup_eq_top' c U V hUV hU hV
