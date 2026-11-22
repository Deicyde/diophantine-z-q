/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_CurveModel_finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_CurveModel_exists_divisorClassMap
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_CurveModel_finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicCurve

namespace CurveModelBridge

theorem comap_hom_eq_map_inv {X Y : Scheme.{u}} (e : Y ≅ X) (J : X.IdealSheafData) :
    J.comap e.hom = J.map e.inv := by
  apply le_antisymm
  · rw [Scheme.IdealSheafData.le_map_iff_comap_le, ← Scheme.IdealSheafData.comap_comp, e.inv_hom_id,
      Scheme.IdealSheafData.comap_id]
  · have h : ((J.map e.inv).comap e.inv).comap e.hom ≤ J.comap e.hom :=
      Scheme.IdealSheafData.comap_mono e.hom (Scheme.IdealSheafData.comap_map_le J e.inv)
    rwa [← Scheme.IdealSheafData.comap_comp, e.hom_inv_id, Scheme.IdealSheafData.comap_id] at h

theorem ker_comap_iso {X Y T : Scheme.{u}} (e : Y ≅ X) (p : T ⟶ X) :
    p.ker.comap e.hom = (p ≫ e.inv).ker := by
  rw [comap_hom_eq_map_inv, Scheme.Hom.ker_comp]

theorem comap_prod {X Y : Scheme.{u}} (f : Y ⟶ X) {n : ℕ} (I : Fin n → X.IdealSheafData) :
    (∏ i, I i).comap f = ∏ i, (I i).comap f := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Scheme.IdealSheafData.one_eq_top]
    exact Scheme.IdealSheafData.comap_top f
  | succ n ih =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Scheme.IdealSheafData.comap_mulFLT, ih]

theorem isInvertible_prod {X : Scheme.{u}} {n : ℕ} (I : Fin n → X.IdealSheafData)
    (h : ∀ i, (I i).IsCartierFLT) : (∏ i, I i).IsCartierFLT := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Scheme.IdealSheafData.one_eq_top]
    exact Scheme.IdealSheafData.isInvertible_topFLT
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    exact (h 0).mul (ih _ fun i => h i.succ)

section model

variable {K : Type u} [Field K] [IsAlgClosed K] {F : Type u} [Field F] [Algebra K F]

abbrev Pt (M : CurveModel K F) := {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _}

omit [IsAlgClosed K] in
theorem isInvertible_ker (M : CurveModel K F) (p : Pt M) : p.1.ker.IsCartierFLT :=
  Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := M.toBase) p.1 p.2

theorem cl_prod_ker (M : CurveModel K F) (cl : M.C.Modules → Pic K F)
    (h_iso : ∀ L L' : M.C.Modules, Scheme.Modules.IsInvertible L → Nonempty (L ≅ L') → cl L = cl L')
    (h_tensor : ∀ L L' : M.C.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
      cl (L ⊗ L') = cl L + cl L')
    (h_ker : ∀ (P : Pt M) (n : ℕ),
      cl (((P.1.ker) ^ n).invModule) = QuotientAddGroup.mk (n • Finsupp.single (M.pointEquivPlace P) (1 : ℤ)) ∧
        cl (((P.1.ker) ^ n).module) = QuotientAddGroup.mk (-(n • Finsupp.single (M.pointEquivPlace P) (1 : ℤ))))
    {n : ℕ} (P : Fin n → Pt M) :
    cl ((∏ m, (P m).1.ker).invModule) =
        QuotientAddGroup.mk (∑ m, Finsupp.single (M.pointEquivPlace (P m)) (1 : ℤ)) ∧
      cl ((∏ m, (P m).1.ker).module) =
        QuotientAddGroup.mk (-(∑ m, Finsupp.single (M.pointEquivPlace (P m)) (1 : ℤ))) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty, neg_zero,
      Scheme.IdealSheafData.one_eq_top, QuotientAddGroup.mk_zero]
    have htop : (⊤ : M.C.IdealSheafData).IsCartierFLT := Scheme.IdealSheafData.isInvertible_topFLT
    constructor
    · have h2 : cl ((⊤ * ⊤ : M.C.IdealSheafData).invModule) =
          cl ((⊤ : M.C.IdealSheafData).invModule ⊗ (⊤ : M.C.IdealSheafData).invModule) :=
        h_iso _ _ (htop.mul htop).isInvertible_invModule
          (Scheme.IdealSheafData.IsCartierFLT.nonempty_mul_invModule_iso_tensor htop htop)
      rw [Scheme.IdealSheafData.top_mul,
        h_tensor _ _ htop.isInvertible_invModule htop.isInvertible_invModule] at h2
      exact (add_left_cancel ((add_zero _).trans h2)).symm
    · have h2 : cl ((⊤ * ⊤ : M.C.IdealSheafData).module) =
          cl ((⊤ : M.C.IdealSheafData).module ⊗ (⊤ : M.C.IdealSheafData).module) :=
        h_iso _ _ (htop.mul htop).isInvertible_module
          (Scheme.IdealSheafData.IsCartierFLT.nonempty_mul_module_iso_tensor htop htop)
      rw [Scheme.IdealSheafData.top_mul,
        h_tensor _ _ htop.isInvertible_module htop.isInvertible_module] at h2
      exact (add_left_cancel ((add_zero _).trans h2)).symm
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i => P i.succ)
    have h0 : (P 0).1.ker.IsCartierFLT := isInvertible_ker M (P 0)
    have hrest : (∏ i : Fin n, (P i.succ).1.ker).IsCartierFLT :=
      isInvertible_prod _ fun i => isInvertible_ker M (P i.succ)
    obtain ⟨hk1, hk2⟩ := h_ker (P 0) 1
    simp only [pow_one, one_smul] at hk1 hk2
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
    constructor
    · rw [h_iso _ _ (h0.mul hrest).isInvertible_invModule
          (Scheme.IdealSheafData.IsCartierFLT.nonempty_mul_invModule_iso_tensor h0 hrest),
        h_tensor _ _ h0.isInvertible_invModule hrest.isInvertible_invModule, hk1, ih1,
        ← QuotientAddGroup.mk_add]
    · rw [h_iso _ _ (h0.mul hrest).isInvertible_module
          (Scheme.IdealSheafData.IsCartierFLT.nonempty_mul_module_iso_tensor h0 hrest),
        h_tensor _ _ h0.isInvertible_module hrest.isInvertible_module, hk2, ih2,
        ← QuotientAddGroup.mk_add, ← neg_add]

theorem model_case (M : CurveModel K F) {a b : ℕ} (P : Fin a → Pt M) (Q : Fin b → Pt M)
    (𝒱 : M.C.TwoAffineOpenCover) :
    Module.Finite K (𝒱.sectionsOf M.toBase ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module)).H0 ∧
    Module.Finite K (𝒱.sectionsOf M.toBase ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module)).H1 ∧
    Module.finrank K (𝒱.sectionsOf M.toBase
        ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module)).H0 =
      ell ((∑ m, Finsupp.single (M.pointEquivPlace (P m)) (1 : ℤ)) -
           ∑ j, Finsupp.single (M.pointEquivPlace (Q j)) (1 : ℤ)) := by
  haveI : IsCurveOver K F :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  obtain ⟨cl, h_iso, h_tensor, -, h_ker, h_coh⟩ := CurveModel.exists_divisorClassMap M
  have hIP : (∏ m, (P m).1.ker).IsCartierFLT := isInvertible_prod _ fun m => isInvertible_ker M (P m)
  have hIQ : (∏ j, (Q j).1.ker).IsCartierFLT := isInvertible_prod _ fun j => isInvertible_ker M (Q j)
  obtain ⟨hclP, -⟩ := cl_prod_ker M cl h_iso h_tensor h_ker P
  obtain ⟨-, hclQ⟩ := cl_prod_ker M cl h_iso h_tensor h_ker Q
  have hinv : Scheme.Modules.IsInvertible ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module) :=
    hIP.isInvertible_invModule.tensor hIQ.isInvertible_module
  have hcl : QuotientAddGroup.mk ((∑ m, Finsupp.single (M.pointEquivPlace (P m)) (1 : ℤ)) -
        ∑ j, Finsupp.single (M.pointEquivPlace (Q j)) (1 : ℤ)) =
      cl ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module) := by
    rw [h_tensor _ _ hIP.isInvertible_invModule hIQ.isInvertible_module, hclP, hclQ,
      ← QuotientAddGroup.mk_add, sub_eq_add_neg]
  obtain ⟨hfin0, hfin1, hrank, -⟩ := h_coh 𝒱 _ hinv _ hcl
  exact ⟨hfin0, hfin1, hrank⟩

end model

end CurveModelBridge

open CurveModelBridge in
theorem solution
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
              rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (Q j).2⟩) (1 : ℤ)) := by

  have hP' : ∀ m, ((P m).1 ≫ e.inv) ≫ M.toBase = 𝟙 _ := fun m => by
    rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (P m).2
  have hQ' : ∀ j, ((Q j).1 ≫ e.inv) ≫ M.toBase = 𝟙 _ := fun j => by
    rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (Q j).2
  let P' : Fin a → Pt M := fun m => ⟨(P m).1 ≫ e.inv, hP' m⟩
  let Q' : Fin b → Pt M := fun j => ⟨(Q j).1 ≫ e.inv, hQ' j⟩

  have hIP : (∏ m, (P m).1.ker).IsCartierFLT :=
    isInvertible_prod _ fun m => Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := x) (P m).1 (P m).2
  have hIQ : (∏ j, (Q j).1.ker).IsCartierFLT :=
    isInvertible_prod _ fun j => Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := x) (Q j).1 (Q j).2
  have hIP' : (∏ m, (P' m).1.ker).IsCartierFLT := isInvertible_prod _ fun m => isInvertible_ker M (P' m)
  have hIQ' : (∏ j, (Q' j).1.ker).IsCartierFLT := isInvertible_prod _ fun j => isInvertible_ker M (Q' j)

  have hcP : (∏ m, (P m).1.ker).comap e.hom = ∏ m, (P' m).1.ker := by
    rw [comap_prod]; simp only [ker_comap_iso, P']
  have hcQ : (∏ j, (Q j).1.ker).comap e.hom = ∏ j, (Q' j).1.ker := by
    rw [comap_prod]; simp only [ker_comap_iso, Q']
  have hcPinv : ((∏ m, (P m).1.ker).comap e.hom).IsCartierFLT := by rw [hcP]; exact hIP'
  have hcQinv : ((∏ j, (Q j).1.ker).comap e.hom).IsCartierFLT := by rw [hcQ]; exact hIQ'

  obtain ⟨i1⟩ := Scheme.IdealSheafData.IsCartierFLT.nonempty_pullback_invModule_iso e.hom hIP hcPinv
  haveI := Scheme.IdealSheafData.IsCartierFLT.isIso_pullbackModuleComparison e.hom hIQ hcQinv
  have eN : ((∏ m, (P' m).1.ker).invModule ⊗ (∏ j, (Q' j).1.ker).module) ≅
      (Scheme.Modules.pullback e.hom).obj ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module) :=
    eqToIso (by rw [hcP, hcQ]) ≪≫
      (tensorIso i1.symm (asIso ((∏ j, (Q j).1.ker).pullbackModuleComparison e.hom)).symm) ≪≫
      (Scheme.Modules.pullbackTensorObjIsoFLT e.hom _ _).symm

  obtain ⟨𝒱₀, -, -, ⟨f0⟩, ⟨f1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso M.toBase x e he 𝒱 _ _ eN
  obtain ⟨hfin0, hfin1, hrank⟩ := model_case M P' Q' 𝒱₀
  refine ⟨?_, ?_, ?_⟩
  · haveI := hfin0; exact Module.Finite.equiv f0
  · haveI := hfin1; exact Module.Finite.equiv f1
  · rw [← f0.finrank_eq]; exact hrank
