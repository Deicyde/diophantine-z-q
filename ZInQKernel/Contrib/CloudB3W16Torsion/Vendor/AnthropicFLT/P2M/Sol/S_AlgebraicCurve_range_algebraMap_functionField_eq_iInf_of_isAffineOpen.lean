/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_IsAffineOpen_range_algebraMap_functionField_eq_iInf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u

theorem solution
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    (algebraMap Γ(C, U) C.functionField).range =
      ⨅ (v : AlgebraicCurve.Place K C.functionField)
        (_ : ∃ x : C, x ∈ U ∧ IsClosed ({x} : Set C) ∧
          (algebraMap (C.presheaf.stalk x) C.functionField).range =
            v.toValuationSubring.toSubring),
        v.toValuationSubring.toSubring := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  rw [hU.range_algebraMap_functionField_eq_iInf]
  apply le_antisymm
  ·
    refine le_iInf₂ fun v hv => ?_
    obtain ⟨x, hxU, -, hrange⟩ := hv
    rw [← hrange]
    exact iInf₂_le x hxU
  ·
    refine le_iInf₂ fun x hxU => ?_
    by_cases hη : x = genericPoint C
    ·
      subst hη
      intro f _
      refine ⟨f, ?_⟩
      change (C.presheaf.stalkSpecializes (specializes_refl _)).hom f = f
      rw [TopCat.Presheaf.stalkSpecializes_refl]
      rfl
    · have hxcl : IsClosed ({x} : Set C) := isClosed_singleton_of_ne_genericPoint c x hη
      obtain ⟨v, hv⟩ := exists_place_range_stalk_eq c x hxcl
      rw [hv]
      exact iInf₂_le v ⟨x, hxU, hxcl, hv⟩
