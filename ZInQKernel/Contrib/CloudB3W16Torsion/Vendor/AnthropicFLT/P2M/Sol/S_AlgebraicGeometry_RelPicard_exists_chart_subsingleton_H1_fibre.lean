/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_eulerChar_sectionsOf_tensor_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_isAffineOpen_sup_eq_top
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_isAffineOpen_forall_mem_of_finset
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_CurveModel_finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Opposite
open AlgebraicGeometry
-- Original source-local namespace open deferred until after its declaration.
open AlgebraicGeometry.RelPicard
-- Original source-local namespace open deferred until after its declaration.
open NeronModelInfra
open AlgebraicCurve hiding genus

noncomputable section

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral Scheme.Hom GeometricallyIntegral Scheme.Modules.presheaf Scheme.Modules.Hom Spec IsIntegral Scheme Scheme.Modules.Hom.app IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible RelEffCartierDiv mapOnProdOver RelEffCartierDiv.pullbackAlong_comp Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap prodKerGraph graphOver graphOver_snd Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.IdealSheafData.IsInvertible Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed prodKerGraph_comap_mapOnProdOver Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one)
namespace RelPicard
export _root_.AlgebraicGeometry.RelPicard (baseChangeSnd rigSection RigidifiedLineBundle fibreAt IsAlgEquivZero FibrewiseAlgEquivZero sectionTwist fibreModule sectionFibrePoint HasChartSections nonempty_pullback_sectionTwist_iso exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero_of_isAlgClosed)
namespace K7cov35
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry

variable {R : Type u} [CommRing R]

section Probe
variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c] [SmoothOfRelativeDimension 1 c]
  [GeometricallyIntegral c] {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
example : IsProper (pullback.snd c x) := inferInstance
example : IsSeparated (pullback.snd c x) := inferInstance
example : SmoothOfRelativeDimension 1 (pullback.snd c x) := inferInstance
example : GeometricallyIntegral (pullback.snd c x) := inferInstance
example : IsIntegral (pullback c x) :=
  GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback c x)
example : IsLocalRing k := inferInstance
example : (𝟙_ (pullback c x).Modules)
    = (SheafOfModules.unit (pullback c x).ringCatSheaf : (pullback c x).Modules) := rfl
example : fibreAt c (𝟙 _) x = pullback.snd (pullback.snd c (𝟙 _)) x := rfl
example (X : Scheme.{u}) (U : X.Opens) : (𝟙 X) ⁻¹ᵁ U = U := rfl
end Probe

theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

theorem nonempty_linearEquiv_of_iso {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of R))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Nonempty ((𝒱.sectionsOf x M).H0 ≃ₗ[R] (𝒱.sectionsOf x M').H0) ∧
      Nonempty ((𝒱.sectionsOf x M).H1 ≃ₗ[R] (𝒱.sectionsOf x M').H1) := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X) (Category.id_comp x)
      𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain rfl : 𝒱₂ = 𝒱 := cover_ext h0 h1
  exact ⟨⟨e0⟩, ⟨e1⟩⟩

theorem eulerChar_congr {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    (Module.finrank k (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x M).H1 =
      (Module.finrank k (𝒱.sectionsOf x M').H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x M').H1 := by
  obtain ⟨⟨e0⟩, ⟨e1⟩⟩ := nonempty_linearEquiv_of_iso x 𝒱 e
  rw [e0.finrank_eq, e1.finrank_eq]

theorem finrank_H1_congr {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Module.finrank k (𝒱.sectionsOf x M).H1 = Module.finrank k (𝒱.sectionsOf x M').H1 := by
  obtain ⟨-, ⟨e1⟩⟩ := nonempty_linearEquiv_of_iso x 𝒱 e
  exact e1.finrank_eq

def isoPullbackInvOfIso {X Y : Scheme.{u}} (φ : X ≅ Y) {M : X.Modules} {N : Y.Modules}
    (e : M ≅ (Scheme.Modules.pullback φ.hom).obj N) : N ≅ (Scheme.Modules.pullback φ.inv).obj M :=
  ((Scheme.Modules.pullbackId Y).app N).symm ≪≫
    (Scheme.Modules.pullbackCongr φ.inv_hom_id.symm).app N ≪≫
    ((Scheme.Modules.pullbackComp φ.inv φ.hom).app N).symm ≪≫
    (Scheme.Modules.pullback φ.inv).mapIso e.symm

section FibreIso

variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
  {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
  (hx : s ≫ t = x)

def fibreIso : pullback (pullback.snd c t) s ≅ pullback c x :=
  pullbackLeftPullbackSndIso c t s ≪≫ pullback.congrHom rfl hx

@[reassoc]
theorem fibreIso_hom_snd : (fibreIso c t s x hx).hom ≫ pullback.snd c x = fibreAt c t s := by
  subst hx
  simp [fibreIso, fibreAt, pullback.congrHom_hom]

@[reassoc]
theorem fibreIso_hom_fst :
    (fibreIso c t s x hx).hom ≫ pullback.fst c x = pullback.fst (pullback.snd c t) s ≫ pullback.fst c t := by
  subst hx
  simp [fibreIso, pullback.congrHom_hom]

theorem fibreIso_inv_fibreAt : (fibreIso c t s x hx).inv ≫ fibreAt c t s = pullback.snd c x := by
  rw [← fibreIso_hom_snd c t s x hx, Iso.inv_hom_id_assoc]

theorem fibreIso_hom_baseChangeSnd :
    (fibreIso c t s x hx).hom ≫ baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t)
      = pullback.fst (pullback.snd c t) s := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    unfold baseChangeSnd
    rw [pullback.lift_fst, ← Category.assoc, fibreIso_hom_fst, Category.assoc, Category.comp_id]
  · rw [Category.assoc]
    unfold baseChangeSnd
    rw [pullback.lift_snd, ← Category.assoc, fibreIso_hom_snd, pullback.condition]
    rfl

def fibreModuleIso (F : (pullback c t).Modules) :
    fibreModule c t s F ≅ (Scheme.Modules.pullback (fibreIso c t s x hx).hom).obj
      ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).obj F) :=
  (Scheme.Modules.pullbackCongr (fibreIso_hom_baseChangeSnd c t s x hx).symm).app F ≪≫
    ((Scheme.Modules.pullbackComp (fibreIso c t s x hx).hom
      (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).app F).symm

def fibreUnitIso :
    (𝟙_ (pullback (pullback.snd c t) s).Modules) ≅
      (Scheme.Modules.pullback (fibreIso c t s x hx).hom).obj (𝟙_ (pullback c x).Modules) :=
  (Scheme.Modules.pullbackTensorUnitObjIso (fibreIso c t s x hx).hom).symm

variable [IsSeparated c] [SmoothOfRelativeDimension 1 c] (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

theorem nonempty_chartModule_iso (r : ℕ) {e : ℕ} (D : RelEffCartierDiv c e t) :
    Nonempty (fibreModule c t s (sectionTwist c ε t r ⊗ D.idealModule) ≅
      (Scheme.Modules.pullback (fibreIso c t s x hx).hom).obj
        (sectionTwist c ε x r ⊗ (D.pullbackAlong s hx).idealModule)) := by
  obtain ⟨eT⟩ := nonempty_pullback_sectionTwist_iso R c ε (⟨s, hx⟩ : SchemeHomOver x t) r
  have hI : D.I.IsInvertible := D.isInvertible_I
  have hI' : (D.I.comap (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).IsInvertible :=
    (D.pullbackAlong s hx).isInvertible_I
  let eI : (Scheme.Modules.pullback (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).obj D.idealModule ≅
      (D.pullbackAlong s hx).idealModule :=
    @asIso _ _ _ _ (D.I.pullbackModuleComparison (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t)))
      (Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison
        (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t)) hI hI')
  exact ⟨fibreModuleIso c t s x hx _ ≪≫ (Scheme.Modules.pullback (fibreIso c t s x hx).hom).mapIso
    (Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (eT ⊗ᵢ eI))⟩

theorem exists_cover_chart_of_cover (r : ℕ) {e : ℕ} (D : RelEffCartierDiv c e t)
    (𝒱 : (pullback c x).TwoAffineOpenCover) :
    ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (sectionTwist c ε t r ⊗ D.idealModule))).H0 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x) (sectionTwist c ε x r ⊗ (D.pullbackAlong s hx).idealModule)).H0) ∧
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (sectionTwist c ε t r ⊗ D.idealModule))).H1 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x) (sectionTwist c ε x r ⊗ (D.pullbackAlong s hx).idealModule)).H1) := by
  obtain ⟨eM⟩ := nonempty_chartModule_iso c t s x hx ε r D
  obtain ⟨𝒲, -, -, h0, h1⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t s) (pullback.snd c x) (fibreIso c t s x hx) (fibreIso_hom_snd c t s x hx) 𝒱 _ _ eM
  exact ⟨𝒲, h0, h1⟩

theorem exists_cover_of_cover_chart (r : ℕ) {e : ℕ} (D : RelEffCartierDiv c e t)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) :
    ∃ 𝒱 : (pullback c x).TwoAffineOpenCover,
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (sectionTwist c ε t r ⊗ D.idealModule))).H0 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x) (sectionTwist c ε x r ⊗ (D.pullbackAlong s hx).idealModule)).H0) ∧
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (sectionTwist c ε t r ⊗ D.idealModule))).H1 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x) (sectionTwist c ε x r ⊗ (D.pullbackAlong s hx).idealModule)).H1) := by
  obtain ⟨eM⟩ := nonempty_chartModule_iso c t s x hx ε r D
  obtain ⟨𝒱, -, -, ⟨h0⟩, ⟨h1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (pullback.snd c x) (fibreAt c t s) (fibreIso c t s x hx).symm (fibreIso_inv_fibreAt c t s x hx) 𝒲 _ _
    (isoPullbackInvOfIso (fibreIso c t s x hx) eM)
  exact ⟨𝒱, ⟨h0.symm⟩, ⟨h1.symm⟩⟩

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
include hx in

theorem exists_cover_of_cover_unit (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) :
    ∃ 𝒱 : (pullback c x).TwoAffineOpenCover,
      Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (𝟙_ _)).H0
          = Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (𝟙_ _)).H0 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (𝟙_ _)).H1
          = Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (𝟙_ _)).H1 := by
  obtain ⟨𝒱, -, -, ⟨e0⟩, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (pullback.snd c x) (fibreAt c t s) (fibreIso c t s x hx).symm (fibreIso_inv_fibreAt c t s x hx) 𝒲 _ _
    (isoPullbackInvOfIso (fibreIso c t s x hx) (fibreUnitIso c t s x hx))
  exact ⟨𝒱, e0.finrank_eq.symm, e1.finrank_eq.symm⟩

end FibreIso

end AlgebraicGeometry.RelPicard.K7cov35
open _root_.P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre.AlgebraicGeometry
open _root_.P2MW.S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre.AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral Scheme.Hom GeometricallyIntegral Scheme.Modules.presheaf Scheme.Modules.Hom Spec IsIntegral Scheme Scheme.Modules.Hom.app IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible RelEffCartierDiv mapOnProdOver RelEffCartierDiv.pullbackAlong_comp Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap prodKerGraph graphOver graphOver_snd Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.IdealSheafData.IsInvertible Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed prodKerGraph_comap_mapOnProdOver Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one)
namespace RelPicard
export _root_.AlgebraicGeometry.RelPicard (baseChangeSnd rigSection RigidifiedLineBundle fibreAt IsAlgEquivZero FibrewiseAlgEquivZero sectionTwist fibreModule sectionFibrePoint HasChartSections nonempty_pullback_sectionTwist_iso exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero_of_isAlgClosed)
namespace K7cov35
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry

def sectionOfGlobal {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) : M.val.sections :=
  ⟨fun U => (Scheme.Modules.presheaf M).map (homOfLE (le_top : U.unop ≤ ⊤)).op σ,
   fun {U V} f => by
     show (Scheme.Modules.presheaf M).map f ((Scheme.Modules.presheaf M).map (homOfLE (le_top : U.unop ≤ ⊤)).op σ) =
       (Scheme.Modules.presheaf M).map (homOfLE (le_top : V.unop ≤ ⊤)).op σ
     have hg : (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f = (homOfLE (le_top : V.unop ≤ ⊤)).op :=
       Subsingleton.elim _ _
     rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, hg]⟩

theorem sectionOfGlobal_top {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) :
    (sectionOfGlobal M σ).val (op ⊤) = σ := by
  show (Scheme.Modules.presheaf M).map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op σ = σ
  have h1 : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) := Subsingleton.elim _ _
  rw [h1, CategoryTheory.Functor.map_id]
  rfl

theorem exists_hom_ne_zero {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) (hσ : σ ≠ 0) :
    ∃ s : 𝟙_ X.Modules ⟶ M, s ≠ 0 := by
  obtain ⟨s, hs⟩ : ∃ s : 𝟙_ X.Modules ⟶ M, (SheafOfModules.unitHomEquiv M) s = sectionOfGlobal M σ :=
    ⟨(SheafOfModules.unitHomEquiv M).symm (sectionOfGlobal M σ), Equiv.apply_symm_apply _ _⟩
  refine ⟨s, fun h0 => hσ ?_⟩
  have e2 : (sectionOfGlobal M σ).val (op ⊤) = σ := sectionOfGlobal_top M σ
  have e3 : (sectionOfGlobal M σ).val (op ⊤) = (Scheme.Modules.Hom.app s ⊤) (1 : Γ(X, ⊤)) := by
    rw [← hs]
    rfl
  rw [← e2, e3, h0, Scheme.Modules.Hom.zero_app]
  rfl

theorem exists_section_ne_zero {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    (𝒱 : X.TwoAffineOpenCover) (M : X.Modules) (h : Nontrivial (𝒱.sectionsOf x M).H0) :
    ∃ s : 𝟙_ X.Modules ⟶ M, s ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_ne (0 : (𝒱.sectionsOf x M).H0)
  obtain ⟨eΓ, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 x M
  have hσ : eΓ.symm y ≠ 0 := fun h => hy (by rw [← eΓ.apply_symm_apply y, h, map_zero])
  exact exists_hom_ne_zero M (eΓ.symm y) hσ

end AlgebraicGeometry.RelPicard.K7cov35

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral Scheme.Hom GeometricallyIntegral Scheme.Modules.presheaf Scheme.Modules.Hom Spec IsIntegral Scheme Scheme.Modules.Hom.app IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible RelEffCartierDiv mapOnProdOver RelEffCartierDiv.pullbackAlong_comp Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap prodKerGraph graphOver graphOver_snd Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.IdealSheafData.IsInvertible Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed prodKerGraph_comap_mapOnProdOver Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one)
namespace RelPicard
export _root_.AlgebraicGeometry.RelPicard (baseChangeSnd rigSection RigidifiedLineBundle fibreAt IsAlgEquivZero FibrewiseAlgEquivZero sectionTwist fibreModule sectionFibrePoint HasChartSections nonempty_pullback_sectionTwist_iso exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero_of_isAlgClosed)
namespace K7cov35
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry

theorem geom
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (n g r : ℕ) (hgr : 2 * g < r)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hγ : HasChartSections c γ)
    (Dγ : Fin n → RelEffCartierDiv c (r - g) (𝟙 (Spec (CommRingCat.of R))))
    (hDγ : ∀ i, (Dγ i).I = prodKerGraph c (fun j => (γ i j).1) (fun j => (γ i j).2))
    (hχ : ∀ (i : Fin n) (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ (Dγ i).idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ (Dγ i).idealModule))).H1 = 1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ T) :
    ∃ i : Fin n, ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
        (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1 := by

  haveI : IsSeparated c := inferInstance
  haveI : IsIntegral (pullback c (s ≫ t)) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback c (s ≫ t))
  haveI : IsProper (pullback.snd c (s ≫ t)) := inferInstance
  let φ : pullback (pullback.snd c t) s ≅ pullback c (s ≫ t) := fibreIso c t s (s ≫ t) rfl

  obtain ⟨U, V, hU, hV, hUV, hsup⟩ := AlgebraicCurve.exists_isAffineOpen_sup_eq_top (pullback.snd c (s ≫ t))
    (fun F => AlgebraicCurve.exists_isAffineOpen_forall_mem_of_finset (pullback.snd c (s ≫ t)) F)
  let 𝒱 : (pullback c (s ≫ t)).TwoAffineOpenCover := ⟨U, V, hU, hV, hsup, hUV⟩

  let LY : (pullback c (s ≫ t)).Modules :=
    (Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj L.L
  let TwY : (pullback c (s ≫ t)).Modules := sectionTwist c ε (s ≫ t) r
  have hσ : rigSection c (s ≫ t) ε ≫ pullback.snd c (s ≫ t) = 𝟙 _ := pullback.lift_snd _ _ _
  have hLY : Scheme.Modules.IsInvertible LY := L.isInvertible.pullback _
  have hTwY : Scheme.Modules.IsInvertible TwY :=
    ((Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c (s ≫ t) ε) hσ).pow r).isInvertible_invModule
  have hLT : Scheme.Modules.IsInvertible (LY ⊗ TwY) := hLY.tensor hTwY

  have hAEZ : IsAlgEquivZero (pullback.snd c (s ≫ t)) LY :=
    (((hL K s).pullback φ.inv (fibreIso_inv_fibreAt c t s (s ≫ t) rfl)).of_iso
      (isoPullbackInvOfIso φ (fibreModuleIso c t s (s ≫ t) rfl L.L)).symm)

  obtain ⟨eT⟩ := nonempty_pullback_sectionTwist_iso R c ε (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t) r
  let eLT : fibreModule c t s (L.L ⊗ sectionTwist c ε t r) ≅ (Scheme.Modules.pullback φ.hom).obj (LY ⊗ TwY) :=
    Scheme.Modules.pullbackTensorObjIso (pullback.fst (pullback.snd c t) s) L.L (sectionTwist c ε t r) ≪≫
      (fibreModuleIso c t s (s ≫ t) rfl L.L ⊗ᵢ
        (fibreModuleIso c t s (s ≫ t) rfl (sectionTwist c ε t r) ≪≫ (Scheme.Modules.pullback φ.hom).mapIso eT)) ≪≫
      (Scheme.Modules.pullbackTensorObjIso φ.hom LY TwY).symm

  have hr1 : 2 * g ≤ r + 1 := by omega
  have hcut := subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero_of_isAlgClosed
    R c ε g hg L hL r hr1 K s
  obtain ⟨𝒲₁, -, -, ⟨f0⟩, ⟨f1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t s) (pullback.snd c (s ≫ t)) φ (fibreIso_hom_snd c t s (s ≫ t) rfl) 𝒱 (LY ⊗ TwY)
    (fibreModule c t s (L.L ⊗ sectionTwist c ε t r)) eLT
  obtain ⟨hs1, hf0⟩ := hcut 𝒲₁
  have h0Y : Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ TwY)).H0 = r + 1 - g :=
    f0.finrank_eq.symm.trans hf0
  have h1Y : Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ TwY)).H1 = 0 := by
    haveI : Subsingleton (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ TwY)).H1 :=
      Equiv.subsingleton f1.symm.toEquiv
    exact Module.finrank_zero_of_subsingleton

  obtain ⟨hH1u, hH0u⟩ := Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one K
    (pullback.snd c (s ≫ t)) g (hg K (s ≫ t)) 𝒱
  have hH1u' : Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (𝟙_ (pullback c (s ≫ t)).Modules)).H1 = g :=
    hH1u
  have hH0u' : Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (𝟙_ (pullback c (s ≫ t)).Modules)).H0 = 1 :=
    hH0u

  have hpos : 0 < Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ TwY)).H0 := by
    rw [h0Y]; omega
  have hnt : Nontrivial (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ TwY)).H0 :=
    Module.nontrivial_of_finrank_pos hpos
  obtain ⟨sec, hsec⟩ := exists_section_ne_zero (pullback.snd c (s ≫ t)) 𝒱 (LY ⊗ TwY) hnt
  have hχLT : (Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ TwY)).H0 : ℤ)
        - Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ TwY)).H1
      = (Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (𝟙_ (pullback c (s ≫ t)).Modules)).H0 : ℤ)
        - Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (𝟙_ (pullback c (s ≫ t)).Modules)).H1 + r := by
    rw [h0Y, h1Y, hH1u', hH0u']
    omega
  obtain ⟨D, -, ⟨eD, -⟩⟩ := RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq (f := c)
    (s ≫ t) hLT sec hsec 𝒱 r hχLT
  obtain ⟨Pt, hPt, hDI⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed D

  obtain ⟨F, instF, instA, M, e, he, -, hch⟩ := hγ K (s ≫ t)
  haveI : IsCurveOver K F :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have hpt : ∀ m : Fin r, (graphOver c (Pt m) (hPt m) ≫ e.inv) ≫ M.toBase = 𝟙 _ := fun m => by
    rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact graphOver_snd c (Pt m) (hPt m)
  have heff : ∀ v : Place K F, 0 ≤ (∑ m : Fin r, Finsupp.single (M.pointEquivPlace ⟨graphOver c (Pt m) (hPt m) ≫ e.inv, hpt m⟩) (1 : ℤ)) v := by
    classical
    intro v
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_nonneg fun m _ => ?_
    rw [Finsupp.single_apply]
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  have hdeg : Divisor.degree (∑ m : Fin r, Finsupp.single (M.pointEquivPlace ⟨graphOver c (Pt m) (hPt m) ≫ e.inv, hpt m⟩) (1 : ℤ)) = r := by
    rw [map_sum]
    simp only [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  obtain ⟨i, hi⟩ := hch _ heff hdeg

  refine ⟨i, fun 𝒲 => ?_⟩

  have hχi := hχ i
  generalize hEt : (Dγ i).pullbackAlong t (Category.comp_id t) = Et at ⊢
  let Ei : RelEffCartierDiv c (r - g) (s ≫ t) := Et.pullbackAlong s rfl
  have hγx : ∀ j : Fin (r - g), ((s ≫ t) ≫ (γ i j).1) ≫ c = s ≫ t := fun j => by
    rw [Category.assoc, (γ i j).2, Category.comp_id]
  have hEiI : Ei.I = prodKerGraph c (fun j => (s ≫ t) ≫ (γ i j).1) hγx := by
    have h1 : Ei = (Dγ i).pullbackAlong (s ≫ t) (Category.comp_id _) := by
      show Et.pullbackAlong s rfl = _
      rw [← hEt, RelEffCartierDiv.pullbackAlong_comp]
    rw [h1]
    show (Dγ i).I.comap (mapOnProdOver c (s ≫ t) (Category.comp_id _)) = _
    rw [hDγ i]
    exact prodKerGraph_comap_mapOnProdOver (f := c) (fun j => (γ i j).1) (fun j => (γ i j).2) (s ≫ t)
      (Category.comp_id _)
  have hEi : Scheme.Modules.IsInvertible Ei.idealModule := Ei.isInvertible_I.isInvertible_module
  let Nc : (pullback c (s ≫ t)).Modules := TwY ⊗ Ei.idealModule
  have hNc : Scheme.Modules.IsInvertible Nc := hTwY.tensor hEi

  obtain ⟨eCh⟩ := nonempty_chartModule_iso c t s (s ≫ t) rfl ε r Et
  let eF : fibreModule c t s (L.L ⊗ (sectionTwist c ε t r ⊗ Et.idealModule)) ≅
      (Scheme.Modules.pullback φ.hom).obj (LY ⊗ Nc) :=
    Scheme.Modules.pullbackTensorObjIso (pullback.fst (pullback.snd c t) s) L.L (sectionTwist c ε t r ⊗ Et.idealModule) ≪≫
      (fibreModuleIso c t s (s ≫ t) rfl L.L ⊗ᵢ eCh) ≪≫
      (Scheme.Modules.pullbackTensorObjIso φ.hom LY Nc).symm
  obtain ⟨𝒱', -, -, ⟨g0⟩, ⟨g1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (pullback.snd c (s ≫ t)) (fibreAt c t s) φ.symm (fibreIso_inv_fibreAt c t s (s ≫ t) rfl) 𝒲 _ _
    (isoPullbackInvOfIso φ eF)

  suffices hY : Subsingleton (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ Nc)).H1 by
    exact Equiv.subsingleton g1.symm.toEquiv

  have hcast : D.lineBundle ⊗ Ei.idealModule =
      (∏ m : Fin r, (⟨graphOver c (Pt m) (hPt m), graphOver_snd c (Pt m) (hPt m)⟩ :
          {p : Spec (CommRingCat.of K) ⟶ pullback c (s ≫ t) // p ≫ pullback.snd c (s ≫ t) = 𝟙 _}).1.ker).invModule ⊗
        (∏ j : Fin (r - g), (sectionFibrePoint (γ i j) (s ≫ t)).1.ker).module := by
    show D.I.invModule ⊗ Ei.I.module = _
    rw [hDI, hEiI]
    rfl
  let eMN := (α_ LY TwY Ei.idealModule).symm ≪≫ whiskerRightIso eD Ei.idealModule ≪≫ eqToIso hcast
  have hd : Module.Finite K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) ((∏ m : Fin r, (⟨graphOver c (Pt m) (hPt m), graphOver_snd c (Pt m) (hPt m)⟩ :
          {p : Spec (CommRingCat.of K) ⟶ pullback c (s ≫ t) // p ≫ pullback.snd c (s ≫ t) = 𝟙 _}).1.ker).invModule ⊗
        (∏ j : Fin (r - g), (sectionFibrePoint (γ i j) (s ≫ t)).1.ker).module)).H0 ∧
      Module.Finite K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) ((∏ m : Fin r, (⟨graphOver c (Pt m) (hPt m), graphOver_snd c (Pt m) (hPt m)⟩ :
          {p : Spec (CommRingCat.of K) ⟶ pullback c (s ≫ t) // p ≫ pullback.snd c (s ≫ t) = 𝟙 _}).1.ker).invModule ⊗
        (∏ j : Fin (r - g), (sectionFibrePoint (γ i j) (s ≫ t)).1.ker).module)).H1 ∧
      Module.finrank K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) ((∏ m : Fin r, (⟨graphOver c (Pt m) (hPt m), graphOver_snd c (Pt m) (hPt m)⟩ :
          {p : Spec (CommRingCat.of K) ⟶ pullback c (s ≫ t) // p ≫ pullback.snd c (s ≫ t) = 𝟙 _}).1.ker).invModule ⊗
        (∏ j : Fin (r - g), (sectionFibrePoint (γ i j) (s ≫ t)).1.ker).module)).H0 = 1 := by
    obtain ⟨fin0, fin1, hrk⟩ :=
      AlgebraicCurve.CurveModel.finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
        (pullback.snd c (s ≫ t)) M e he
        (fun m : Fin r => (⟨graphOver c (Pt m) (hPt m), graphOver_snd c (Pt m) (hPt m)⟩ :
          {p : Spec (CommRingCat.of K) ⟶ pullback c (s ≫ t) // p ≫ pullback.snd c (s ≫ t) = 𝟙 _}))
        (fun j : Fin (r - g) => sectionFibrePoint (γ i j) (s ≫ t)) 𝒱'
    exact ⟨fin0, fin1, hrk.trans hi⟩
  obtain ⟨fin0, fin1, hrk⟩ := hd
  obtain ⟨⟨k0⟩, ⟨k1⟩⟩ := nonempty_linearEquiv_of_iso (pullback.snd c (s ≫ t)) 𝒱' eMN
  have hM0 : Module.finrank K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ Nc)).H0 = 1 :=
    k0.finrank_eq.trans hrk
  haveI hM1fin : Module.Finite K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ Nc)).H1 :=
    Module.Finite.equiv k1.symm

  have hχc := IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq (pullback.snd c (s ≫ t)) 𝒱' LY Nc hLY hNc hAEZ
  have hχ' : (Module.finrank K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) Nc).H0 : ℤ) -
      Module.finrank K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) Nc).H1 = 1 := by
    show (Module.finrank K (𝒱'.sectionsOf (pullback.snd c (s ≫ t))
        (sectionTwist c ε (s ≫ t) r ⊗ (Et.pullbackAlong s rfl).idealModule)).H0 : ℤ) -
      Module.finrank K (𝒱'.sectionsOf (pullback.snd c (s ≫ t))
        (sectionTwist c ε (s ≫ t) r ⊗ (Et.pullbackAlong s rfl).idealModule)).H1 = 1
    rw [← hEt, RelEffCartierDiv.pullbackAlong_comp]
    obtain ⟨𝒲₀, ⟨w0⟩, ⟨w1⟩⟩ :=
      exists_cover_chart_of_cover c (𝟙 _) (s ≫ t) (s ≫ t) (Category.comp_id _) ε r (Dγ i) 𝒱'
    rw [← w0.finrank_eq, ← w1.finrank_eq]
    exact hχi K (s ≫ t) 𝒲₀
  have hM1 : Module.finrank K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ Nc)).H1 = 0 := by omega
  exact Module.finrank_zero_iff.mp hM1

end AlgebraicGeometry.RelPicard.K7cov35

open AlgebraicGeometry.RelPicard.K7cov35 in
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (n g r : ℕ) (hgr : 2 * g < r)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hγ : HasChartSections c γ)
    (Dγ : Fin n → RelEffCartierDiv c (r - g) (𝟙 (Spec (CommRingCat.of R))))
    (hDγ : ∀ i, (Dγ i).I = prodKerGraph c (fun j => (γ i j).1) (fun j => (γ i j).2))
    (hχ : ∀ (i : Fin n) (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ (Dγ i).idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ (Dγ i).idealModule))).H1 = 1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L)
    (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) :
    ∃ i : Fin n, ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
        (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1 := by

  obtain ⟨i, hi⟩ := geom R c ε n g r hgr hg γ hγ Dγ hDγ hχ t L hL (AlgebraicClosure k)
    (Scheme.TwoAffineOpenCover.specMap k (AlgebraicClosure k) ≫ s)
  refine ⟨i, fun 𝒲 => ?_⟩
  haveI : IsSeparated c := inferInstance
  have hσ : rigSection c t ε ≫ pullback.snd c t = 𝟙 _ := pullback.lift_snd _ _ _
  have hTw : Scheme.Modules.IsInvertible (sectionTwist c ε t r) :=
    ((Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c t ε) hσ).pow r).isInvertible_invModule
  have hF : Scheme.Modules.IsInvertible
      (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)) :=
    L.isInvertible.tensor (hTw.tensor ((Dγ i).pullbackAlong t (Category.comp_id t)).isInvertible_I.isInvertible_module)
  obtain ⟨𝒲', -, hH1⟩ :=
    exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff c t
      (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)) hF s 𝒲
      (AlgebraicClosure k)
  exact hH1.mp (hi 𝒲')

end
