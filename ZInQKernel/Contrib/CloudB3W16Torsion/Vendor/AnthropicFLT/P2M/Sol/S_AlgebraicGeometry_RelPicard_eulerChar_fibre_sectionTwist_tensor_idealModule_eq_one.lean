/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one. Apache-2.0.
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
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_eulerChar_tensor_lineBundle_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one.AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open P2MW.S_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one.AlgebraicGeometry.RelPicard
open NeronModelInfra

noncomputable section

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral Scheme.Hom GeometricallyIntegral Spec IsIntegral Scheme IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit RelEffCartierDiv Scheme.TwoAffineOpenCover Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.IdealSheafData.IsInvertible Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id RelEffCartierDiv.eulerChar_tensor_lineBundle_eq Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one)
namespace RelPicard
export _root_.AlgebraicGeometry.RelPicard (baseChangeSnd rigSection fibreAt sectionIdeal sectionTwist fibreModule Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso nonempty_pullback_sectionTwist_iso)
namespace ChartHypotheses
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

end AlgebraicGeometry.RelPicard.ChartHypotheses

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral Scheme.Hom GeometricallyIntegral Spec IsIntegral Scheme IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit RelEffCartierDiv Scheme.TwoAffineOpenCover Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.IdealSheafData.IsInvertible Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id RelEffCartierDiv.eulerChar_tensor_lineBundle_eq Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one)
namespace RelPicard
export _root_.AlgebraicGeometry.RelPicard (baseChangeSnd rigSection fibreAt sectionIdeal sectionTwist fibreModule Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso nonempty_pullback_sectionTwist_iso)
namespace ChartHypotheses
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry
open AlgebraicCurve hiding genus in
theorem eulerChar_chart_eq_one
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (g e r : ℕ) (hr : g + e = r) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover) :
    (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H0 : ℤ) -
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H1 = 1 := by
  have hx : x ≫ 𝟙 (Spec (CommRingCat.of R)) = x := Category.comp_id x

  obtain ⟨𝒱, ⟨e0⟩, ⟨e1⟩⟩ := exists_cover_of_cover_chart c (𝟙 _) x x hx ε r Dγ 𝒲
  rw [e0.finrank_eq, e1.finrank_eq]

  have hσ : rigSection c x ε ≫ pullback.snd c x = 𝟙 _ := pullback.lift_snd _ _ _
  have hIsec : (sectionIdeal c ε x).IsInvertible :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c x ε) hσ
  have hIr : ((sectionIdeal c ε x) ^ r).IsInvertible := hIsec.pow r
  have hP : Scheme.Modules.IsInvertible (sectionTwist c ε x r) := hIr.isInvertible_invModule
  have hEI : (Dγ.pullbackAlong x hx).I.IsInvertible := (Dγ.pullbackAlong x hx).isInvertible_I
  have hPE : Scheme.Modules.IsInvertible (sectionTwist c ε x r ⊗ (Dγ.pullbackAlong x hx).idealModule) :=
    hP.tensor hEI.isInvertible_module

  have h2b := RelEffCartierDiv.eulerChar_tensor_lineBundle_eq x (Dγ.pullbackAlong x hx)
    (sectionTwist c ε x r ⊗ (Dγ.pullbackAlong x hx).idealModule) hPE 𝒱

  have h2c := eulerChar_congr (pullback.snd c x) 𝒱
    (α_ (sectionTwist c ε x r) (Dγ.pullbackAlong x hx).idealModule (Dγ.pullbackAlong x hx).lineBundle ≪≫
      whiskerLeftIso (sectionTwist c ε x r)
        (β_ _ _ ≪≫ (Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso hEI).some) ≪≫
      ρ_ (sectionTwist c ε x r))

  obtain ⟨hZ, hdeg, -, -⟩ :=
    Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id (rigSection c x ε) hσ r
  have h2d := Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq
    (pullback.snd c x) hIr hZ hdeg (𝟙_ _) (Scheme.Modules.isInvertible_unit _) 𝒱
  have h2d' := eulerChar_congr (M := 𝟙_ _ ⊗ ((sectionIdeal c ε x) ^ r).invModule)
    (M' := sectionTwist c ε x r) (pullback.snd c x) 𝒱 (λ_ (sectionTwist c ε x r))

  haveI : IsIntegral (pullback c x) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback c x)
  obtain ⟨hG1, hG0⟩ := Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
    k (pullback.snd c x) g (hg k x) 𝒱
  change Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (𝟙_ _)).H1 = g at hG1
  change Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (𝟙_ _)).H0 = 1 at hG0

  omega

end AlgebraicGeometry.RelPicard.ChartHypotheses

end
open AlgebraicCurve hiding genus in open CategoryTheory CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one.AlgebraicGeometry _root_.AlgebraicGeometry.RelPicard _root_.P2MW.S_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one.AlgebraicGeometry.RelPicard NeronModelInfra  in

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (g e r : ℕ) (hr : g + e = r) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover) :
    (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H0 : ℤ) -
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H1 = 1 :=
  AlgebraicGeometry.RelPicard.ChartHypotheses.eulerChar_chart_eq_one R c ε g e r hr Dγ hg k x 𝒲
