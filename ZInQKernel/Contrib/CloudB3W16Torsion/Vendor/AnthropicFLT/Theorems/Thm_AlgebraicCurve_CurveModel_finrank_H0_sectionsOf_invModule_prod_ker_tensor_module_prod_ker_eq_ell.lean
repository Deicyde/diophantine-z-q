/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicCurve_CurveModel_finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_CurveModel_finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
theorem AlgebraicCurve.CurveModel.finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    {F : Type u} [Field F] [Algebra K F] (M : CurveModel K F) (e : M.C ≅ X) (he : e.hom ≫ x = M.toBase)
    {a b : ℕ} (P : Fin a → {p : Spec (CommRingCat.of K) ⟶ X // p ≫ x = 𝟙 _})
    (Q : Fin b → {p : Spec (CommRingCat.of K) ⟶ X // p ≫ x = 𝟙 _}) (𝒱 : X.TwoAffineOpenCover) :
    Module.Finite K (𝒱.sectionsOf x ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module)).H0 ∧
    Module.Finite K (𝒱.sectionsOf x ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module)).H1 ∧
    Module.finrank K (𝒱.sectionsOf x
        ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module)).H0 =
      ell ((∑ m, Finsupp.single (M.pointEquivPlace ⟨(P m).1 ≫ e.inv, by
              rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (P m).2⟩) (1 : ℤ)) -
           ∑ j, Finsupp.single (M.pointEquivPlace ⟨(Q j).1 ≫ e.inv, by
              rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (Q j).2⟩) (1 : ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell.solution
