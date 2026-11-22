/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_iso_pullback_of_isAlgClosed. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_isAffineOpen_forall_mem_of_finset
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_iso_pullback_of_isAlgClosed

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra AlgebraicCurve

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : IsCurveOver k L) (_ : Algebra.EssFiniteType k L)
      (M : CurveModel k L) (e : M.C ≅ pullback c s), e.hom ≫ pullback.snd c s = M.toBase := by
  classical

  let Cs : Scheme.{u} := pullback c s
  let cs : Cs ⟶ Spec (CommRingCat.of k) := pullback.snd c s
  haveI : IsIntegral Cs := SmoothProperCurve.isIntegral_pullback_Spec_field R c s
  haveI : IsProper cs := inferInstance
  haveI : SmoothOfRelativeDimension 1 cs := inferInstance

  letI alg : Algebra k Cs.functionField := (baseToFunctionField cs).toAlgebra
  haveI hco : IsCurveOver k Cs.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one cs (RingEquiv.refl _) (fun _ => rfl)
  haveI hft : Algebra.EssFiniteType k Cs.functionField := essFiniteType_functionField cs

  have hplace : ∀ x : closedPoints Cs, ∃ v : Place k Cs.functionField,
      (algebraMap (Cs.presheaf.stalk x.1) Cs.functionField).range = v.toValuationSubring.toSubring :=
    fun x => exists_place_range_stalk_eq cs x.1 (mem_closedPoints_iff.mp x.2)
  choose pl hpl using hplace
  have hinj : Function.Injective pl := fun x y hxy =>
    Subtype.ext (eq_of_range_stalk_eq cs x.1 y.1 (by rw [hpl x, hpl y, hxy]))
  have hsurj : Function.Surjective pl := fun v => by
    obtain ⟨x, hxc, hx⟩ := exists_closedPoint_range_stalk_eq cs v
    refine ⟨⟨x, mem_closedPoints_iff.mpr hxc⟩, Place.ext ?_⟩
    apply ValuationSubring.toSubring_injective
    rw [← hpl, hx]
  refine ⟨Cs.functionField, inferInstance, alg, hco, hft,
    { C := Cs
      toBase := cs
      ffEquiv := RingEquiv.refl _
      ffEquiv_algebraMap := fun _ => rfl
      placeOfPoint := pl
      placeOfPoint_bijective := ⟨hinj, hsurj⟩
      range_stalk_eq := fun x => by
        rw [← hpl x]
        ext f
        simp
      finset_subset_affineOpen := fun F =>
        exists_isAffineOpen_forall_mem_of_finset cs F }, Iso.refl _, ?_⟩
  simp [cs]
