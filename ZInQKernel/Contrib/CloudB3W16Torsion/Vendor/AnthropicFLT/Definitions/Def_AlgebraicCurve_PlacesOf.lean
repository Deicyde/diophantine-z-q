/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Definitions.Def_AlgebraicCurve_PlacesOf. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.FunctionField
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicCurve

variable {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C]

def placesOf (U : C.Opens) :
    letI := (baseToFunctionField c).toAlgebra
    Set (Place K C.functionField) :=
  letI := (baseToFunctionField c).toAlgebra
  {v | ∃ x : C, x ∈ U ∧ IsClosed ({x} : Set C) ∧
    (algebraMap (C.presheaf.stalk x) C.functionField).range = v.toValuationSubring.toSubring}

theorem mem_placesOf_iff (U : C.Opens) :
    letI := (baseToFunctionField c).toAlgebra
    ∀ v : Place K C.functionField, v ∈ placesOf c U ↔ ∃ x : C, x ∈ U ∧ IsClosed ({x} : Set C) ∧
      (algebraMap (C.presheaf.stalk x) C.functionField).range = v.toValuationSubring.toSubring :=
  fun _ => Iff.rfl

theorem placesOf_mono {U V : C.Opens} (h : U ≤ V) :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c U ⊆ placesOf c V := by
  rintro v ⟨x, hxU, hx, hv⟩
  exact ⟨x, h hxU, hx, hv⟩

theorem placesOf_sup (U V : C.Opens) :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c (U ⊔ V) = placesOf c U ∪ placesOf c V := by
  letI := (baseToFunctionField c).toAlgebra
  apply Set.Subset.antisymm
  · rintro v ⟨x, hxUV, hx, hv⟩
    rcases (show x ∈ (U : Set C) ∪ (V : Set C) from hxUV) with h | h
    · exact Or.inl ⟨x, h, hx, hv⟩
    · exact Or.inr ⟨x, h, hx, hv⟩
  · rintro v (h | h)
    · exact placesOf_mono c le_sup_left h
    · exact placesOf_mono c le_sup_right h

theorem placesOf_bot :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c (⊥ : C.Opens) = ∅ := by
  letI := (baseToFunctionField c).toAlgebra
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨x, hx, -, -⟩
  exact hx

end AlgebraicCurve

end
