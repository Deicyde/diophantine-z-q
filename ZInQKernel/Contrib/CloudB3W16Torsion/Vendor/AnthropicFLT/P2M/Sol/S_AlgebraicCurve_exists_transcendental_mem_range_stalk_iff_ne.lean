/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_exists_transcendental_mem_range_stalk_iff_ne. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_not_mem_and_forall_ne_mem
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_exists_transcendental_mem_range_stalk_iff_ne

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u

theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (Q : C) (hQ : IsClosed ({Q} : Set C)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∃ f : C.functionField, Transcendental K f ∧
      ∀ x : C, f ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range ↔ x ≠ Q := by
  letI hKF : Algebra K C.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra

  haveI : IsCurveOver K C.functionField :=
    AlgebraicCurve.isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one c
      (RingEquiv.refl _) (fun _ => rfl)
  haveI := SmoothOfRelativeDimension.smooth 1 c
  haveI : LocallyOfFiniteType c := inferInstance
  haveI : Algebra.EssFiniteType K C.functionField := AlgebraicCurve.essFiniteType_functionField c

  obtain ⟨vQ, hvQ⟩ := AlgebraicCurve.exists_place_range_stalk_eq c Q hQ
  have hC : ConstantsAreBase K C.functionField :=
    AlgebraicCurve.constantsAreBase_of_deg_eq_one vQ (IsCurveOver.deg_eq_one_of_isAlgClosed vQ)

  obtain ⟨f, hfQ, hfw⟩ := AlgebraicCurve.Place.exists_not_mem_and_forall_ne_mem hC vQ
  refine ⟨f, ?_, ?_⟩
  ·
    intro halg
    apply hfQ
    obtain ⟨a, ha⟩ := minpoly.mem_range_of_degree_eq_one K f
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible halg.isIntegral))
    rw [← ha]
    exact vQ.algebraMap_mem' a
  · intro x
    constructor
    · rintro hx rfl
      rw [hvQ] at hx
      exact hfQ hx
    · intro hx
      by_cases hxc : IsClosed ({x} : Set C)
      ·
        obtain ⟨vx, hvx⟩ := AlgebraicCurve.exists_place_range_stalk_eq c x hxc
        have hne : vx ≠ vQ := by
          intro h
          exact hx (AlgebraicCurve.eq_of_range_stalk_eq c x Q (by rw [hvx, hvQ, h]))
        show f ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range
        rw [hvx]
        exact hfw vx hne
      ·
        have hxg : x = genericPoint C := by
          by_contra h
          exact hxc (AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c x h)
        subst hxg
        refine ⟨f, ?_⟩
        change (C.presheaf.stalkSpecializes (genericPoint_specializes (genericPoint C))).hom f = f
        have : C.presheaf.stalkSpecializes (genericPoint_specializes (genericPoint C)) = 𝟙 _ :=
          TopCat.Presheaf.stalkSpecializes_refl _ _
        rw [this]
        rfl
