/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_finrank_H0_unit_fibre_eq_one. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_twoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_finrank_H0_unit_fibre_eq_one

section E6H0Unit
set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
-- Source-local namespace open deferred until its declaration.
open AlgebraicGeometry.RelPicard
open P2MW.S_AlgebraicGeometry_RelPicard_finrank_H0_unit_fibre_eq_one.AlgebraicGeometry.RelPicard

noncomputable section

namespace AlgebraicGeometry
open _root_.P2MW.S_AlgebraicGeometry_RelPicard_finrank_H0_unit_fibre_eq_one.AlgebraicGeometry
export _root_.AlgebraicGeometry (SmoothOfRelativeDimension IsProper GeometricallyIntegral.geometrically_isIntegral GeometricallyIntegral Spec IsIntegral Scheme geometrically Scheme.TwoAffineOpenCover SmoothProperCurve.exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_twoAffineOpenCover Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one)
namespace RelPicard
export _root_.AlgebraicGeometry.RelPicard (toProdSpec toProdSpec_fst fst_toProdSpec)
namespace H0UnitAux
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry

theorem finrank_H0_unit_fibre_eq_one'
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (𝒱 : (pullback c s).TwoAffineOpenCover) :
    Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (𝟙_ (pullback c s).Modules)).H0 = 1 := by

  haveI : IsIntegral (pullback c s) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback c s)

  obtain ⟨G, hG⟩ := SmoothProperCurve.exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_twoAffineOpenCover
    k (pullback.snd c s) 𝒱

  exact (Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
    k (pullback.snd c s) G (fun L _ _ M eM hM Kc g' hRR =>
      hG k (𝟙 _) L M
        (eM ≪≫ ⟨toProdSpec (pullback.snd c s), pullback.fst _ _, toProdSpec_fst _, fst_toProdSpec _⟩)
        (by rw [Iso.trans_hom, Category.assoc]
            erw [pullback.lift_snd]
            exact hM) Kc g' hRR) 𝒱).2

end AlgebraicGeometry.RelPicard.H0UnitAux

open CategoryTheory CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (𝒱 : (pullback c s).TwoAffineOpenCover) :
    Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (𝟙_ (pullback c s).Modules)).H0 = 1 :=
  AlgebraicGeometry.RelPicard.H0UnitAux.finrank_H0_unit_fibre_eq_one' c k s 𝒱

open CategoryTheory CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry in
example {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (k : Type u) [Field k] [IsAlgClosed k] {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : Spec (CommRingCat.of k) ⟶ T) (𝒱 : (pullback c (x ≫ t)).TwoAffineOpenCover) :
    Module.finrank k (𝒱.sectionsOf (pullback.snd c (x ≫ t)) (𝟙_ _)).H0 = 1 :=
  solution c k (x ≫ t) 𝒱

end
end E6H0Unit
