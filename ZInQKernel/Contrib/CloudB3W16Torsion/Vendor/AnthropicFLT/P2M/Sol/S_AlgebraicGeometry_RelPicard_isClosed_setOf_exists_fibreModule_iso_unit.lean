/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_isClosed_setOf_exists_fibreModule_iso_unit. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_TwoChartCech_isClosed_setOf_le_finrank_ker_baseChange
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_finrank_H0_unit_fibre_eq_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_iso_tensorUnit_of_ne_zero
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isClosed_setOf_exists_fibreModule_iso_unit

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_RelPicard_isClosed_setOf_exists_fibreModule_iso_unit.AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open P2MW.S_AlgebraicGeometry_RelPicard_isClosed_setOf_exists_fibreModule_iso_unit.AlgebraicGeometry.RelPicard
open NeronModelInfra
open GoodReductionJacobian
open AlgebraicCurve hiding cechDiff
open CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry
export AlgebraicGeometry (Spec.map_comp IsLocallyNoetherian SmoothOfRelativeDimension.smooth Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension IsProper Scheme.Modules.pullback LocallyOfFiniteType.isLocallyNoetherian GeometricallyIntegral.geometrically_isIntegral GeometricallyIntegral Scheme.Modules.presheaf IsAffineOpen.fromSpec_top Scheme.Modules.Hom IsAffineOpen.SpecMap_appLE_fromSpec LocallyOfFiniteType Spec IsIntegral Scheme Smooth Scheme.Modules.Hom.app Scheme.isoSpec_Spec_inv Flat IsLocallyNoetherian.component_noetherian smoothOfRelativeDimension_isStableUnderBaseChange exists_isAffineOpen_mem_and_subset isAffineOpen_top Scheme.Modules.pullbackId IsAffineOpen Scheme.Modules geometrically Scheme.ΓSpecIso Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit SmoothProperCurve.FiniteMapData Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.TwoAffineOpenCover.isScalarTower_sections Scheme.Modules.pullbackTensorUnitObjIso OModulePresheaf Scheme.TwoAffineOpenCover.flat_sections_of_flat Scheme.Modules.projective_sections_of_locallyTrivial OModulePresheaf.cechFinite_ofModules_of_locallyTrivial OModulePresheaf.cechFinite_toOrderedAffineCover_iff Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 geometricallyIntegral_of_isAlgClosed)
namespace RelPicard
export AlgebraicGeometry.RelPicard (RigidifiedLineBundle fibreAt IsAlgEquivZero FibrewiseAlgEquivZero fibreModule exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField finrank_H0_unit_fibre_eq_one IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero)
namespace UnitClosed
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry

open TensorProduct Opposite

theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

theorem finrank_H0_congr {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Module.finrank k (𝒱.sectionsOf x M).H0 = Module.finrank k (𝒱.sectionsOf x M').H0 := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, -⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X) (Category.id_comp x)
      𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain rfl : 𝒱₂ = 𝒱 := cover_ext h0 h1
  exact e0.finrank_eq

theorem specMap_residueField_base {A : Type u} [CommRing A] (𝔭 : PrimeSpectrum A)
    (p : Spec (CommRingCat.of 𝔭.asIdeal.ResidueField)) :
    (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField).base p = 𝔭 := by
  apply PrimeSpectrum.ext
  have hp : p.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right p.isPrime.ne_top
  change Ideal.comap (algebraMap A 𝔭.asIdeal.ResidueField) p.asIdeal = 𝔭.asIdeal
  rw [hp, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

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

theorem flat_prod {S : Type*} [CommRing S] (M N : Type*) [AddCommGroup M] [Module S M] [AddCommGroup N]
    [Module S N] [Module.Flat S M] [Module.Flat S N] : Module.Flat S (M × N) := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  have hM := (Module.Flat.iff_lTensor_injective'.mp (inferInstance : Module.Flat S M)) I
  have hN := (Module.Flat.iff_lTensor_injective'.mp (inferInstance : Module.Flat S N)) I
  have key' : ∀ (p : M × N) (i : I), TensorProduct.prodLeft S S M N S (LinearMap.lTensor (M × N) I.subtype (p ⊗ₜ i)) =
      ((LinearMap.lTensor M I.subtype).prodMap (LinearMap.lTensor N I.subtype)) (TensorProduct.prodLeft S S M N I (p ⊗ₜ i)) := by
    intro p i
    obtain ⟨m, n⟩ := p
    simp [TensorProduct.prodLeft_tmul, LinearMap.lTensor_tmul]
  have key : ∀ x, TensorProduct.prodLeft S S M N S (LinearMap.lTensor (M × N) I.subtype x) =
      ((LinearMap.lTensor M I.subtype).prodMap (LinearMap.lTensor N I.subtype)) (TensorProduct.prodLeft S S M N I x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul p i => exact key' p i
  intro x y hxy
  apply (TensorProduct.prodLeft S S M N I).injective
  have hxy' := congrArg (TensorProduct.prodLeft S S M N S) hxy
  rw [key, key] at hxy'
  have h1 := congrArg Prod.fst hxy'
  have h2 := congrArg Prod.snd hxy'
  simp only [LinearMap.prodMap_apply] at h1 h2
  exact Prod.ext (hM h1) (hN h2)

theorem isClosed_setOf_le_finrank_ker_cechDiff_baseChange
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of A))
    [IsProper π] [Flat π] (𝒱 : X.TwoAffineOpenCover) (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (n : ℕ) :
    IsClosed {𝔭 : PrimeSpectrum A | n ≤ Module.finrank 𝔭.asIdeal.ResidueField
      (LinearMap.ker ((𝒱.sectionsOf π M).cechDiff.baseChange 𝔭.asIdeal.ResidueField))} := by

  have flatOf : ∀ (U : X.Opens) (hU : IsAffineOpen U),
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U
      Module.Flat A Γ(M, U) := by
    intro U hU
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U
    haveI := Scheme.TwoAffineOpenCover.isScalarTower_sections π M U
    haveI : Module.Flat A Γ(X, U) := Scheme.TwoAffineOpenCover.flat_sections_of_flat π U hU
    haveI : Module.Projective Γ(X, U) Γ(M, U) :=
      Scheme.Modules.projective_sections_of_locallyTrivial _ hM.1 ⟨U, hU⟩
    exact Module.Flat.trans A Γ(X, U) Γ(M, U)
  haveI : Module.Flat A (𝒱.sectionsOf π M).M0 := flatOf _ 𝒱.isAffineOpen_U0
  haveI : Module.Flat A (𝒱.sectionsOf π M).M1 := flatOf _ 𝒱.isAffineOpen_U1
  haveI : Module.Flat A (𝒱.sectionsOf π M).M01 := flatOf _ 𝒱.isAffineOpen_inf
  haveI : Module.Flat A ((𝒱.sectionsOf π M).M0 × (𝒱.sectionsOf π M).M1) := flat_prod _ _

  have hcf := OModulePresheaf.cechFinite_ofModules_of_locallyTrivial π M hM.1 𝒱.toOrderedAffineCover
  obtain ⟨hfin0, hfin1⟩ := (OModulePresheaf.cechFinite_toOrderedAffineCover_iff _ _).mp hcf
  haveI : Module.Finite A (LinearMap.ker (𝒱.sectionsOf π M).cechDiff) := hfin0
  haveI : Module.Finite A ((𝒱.sectionsOf π M).M01 ⧸ LinearMap.range (𝒱.sectionsOf π M).cechDiff) := hfin1
  have h := TwoChartCech.isClosed_setOf_le_finrank_ker_baseChange (𝒱.sectionsOf π M).cechDiff
    (𝟙 (Spec (CommRingCat.of A))) n
  simp at h
  exact h

theorem finrank_H0_fibreModule_unit_eq_one
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H0 = 1 := by

  let φ : pullback (pullback.snd c t) s ≅ pullback c (s ≫ t) := pullbackLeftPullbackSndIso c t s
  have hφ : φ.symm.hom ≫ fibreAt c t s = pullback.snd c (s ≫ t) := by
    rw [Iso.symm_hom, Iso.inv_comp_eq]
    exact (pullbackLeftPullbackSndIso_hom_snd c t s).symm

  have e : (𝟙_ (pullback c (s ≫ t)).Modules) ≅ (Scheme.Modules.pullback φ.symm.hom).obj
      (fibreModule c t s (𝟙_ (pullback c t).Modules)) :=
    (Scheme.Modules.pullbackTensorUnitObjIso φ.symm.hom).symm ≪≫
      (Scheme.Modules.pullback φ.symm.hom).mapIso
        (Scheme.Modules.pullbackTensorUnitObjIso (pullback.fst (pullback.snd c t) s)).symm
  obtain ⟨𝒱, -, -, ⟨e0⟩, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (pullback.snd c (s ≫ t)) (fibreAt c t s) φ.symm hφ 𝒲 _ _ e
  rw [← e0.finrank_eq]
  exact finrank_H0_unit_fibre_eq_one c k (s ≫ t) 𝒱

end AlgebraicGeometry.RelPicard.UnitClosed

open AlgebraicGeometry.RelPicard.UnitClosed TensorProduct in

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) :
    IsClosed {x : T | ∃ (k : Type u) (_ : Field k) (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x ∧
        Nonempty (fibreModule c t s L.L ≅ 𝟙_ (pullback (pullback.snd c t) s).Modules)} := by
  classical
  obtain ⟨𝔉, -⟩ := h𝔉 0
  haveI : Smooth c := SmoothOfRelativeDimension.smooth (n := 1) (f := c)
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t

  have fibre_inst : ∀ {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      IsIntegral (pullback (pullback.snd c t) s) ∧ IsProper (fibreAt c t s) ∧
        SmoothOfRelativeDimension 1 (fibreAt c t s) := by
    intro k _ _ s
    haveI : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
      MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
    haveI : IsProper (pullback.snd c t) := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
    refine ⟨?_, ?_, ?_⟩
    · exact GeometricallyIntegral.geometrically_isIntegral (f := pullback.snd c t) s
        (pullback.fst (pullback.snd c t) s) (pullback.snd (pullback.snd c t) s) (IsPullback.of_hasPullback _ _)
    · exact MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
    · exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance

  have pointwise : ∀ {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      1 ≤ Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H0 →
        Nonempty (fibreModule c t s L.L ≅ 𝟙_ (pullback (pullback.snd c t) s).Modules) := by
    intro k _ _ s 𝒲 h1
    obtain ⟨hint, hprop, hsm⟩ := fibre_inst s
    haveI := hint; haveI := hprop; haveI := hsm

    haveI : Nontrivial (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H0 :=
      Module.nontrivial_of_finrank_pos (R := k) h1
    obtain ⟨y, hy⟩ := exists_ne (0 : (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H0)
    obtain ⟨eΓ, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒲 (fibreAt c t s)
      (fibreModule c t s L.L)
    have hσ : eΓ.symm y ≠ 0 := fun h => hy (by rw [← eΓ.apply_symm_apply y, h, map_zero])
    obtain ⟨σ, hσ0⟩ := exists_hom_ne_zero (fibreModule c t s L.L) (eΓ.symm y) hσ

    haveI : GeometricallyIntegral (fibreAt c t s) := geometricallyIntegral_of_isAlgClosed (fibreAt c t s)
    exact IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero (fibreAt c t s) 𝒲 (L.isInvertible.pullback _)
      (hL k s) σ hσ0

  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  rw [Set.mem_compl_iff, Set.mem_setOf_eq] at hx

  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := (⊤ : T.Opens)) trivial
  haveI : IsNoetherianRing Γ(T, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  letI : Algebra R Γ(T, W) := Scheme.TwoAffineOpenCover.algebraOfHom t W
  set A : Type u := Γ(T, W) with hA
  set j : Spec (CommRingCat.of A) ⟶ T := hW.fromSpec with hjdef
  have hj : j ≫ t = Scheme.TwoAffineOpenCover.specMap R A := by
    have e1 : CommRingCat.ofHom (algebraMap R A) = (Scheme.ΓSpecIso (.of R)).inv ≫ t.appLE ⊤ W le_top := rfl
    rw [hjdef, Scheme.TwoAffineOpenCover.specMap, e1, Spec.map_comp, ← Scheme.isoSpec_Spec_inv,
      ← IsAffineOpen.fromSpec_top, IsAffineOpen.SpecMap_appLE_fromSpec t (isAffineOpen_top _) hW]

  set CA := pullback c (Scheme.TwoAffineOpenCover.specMap R A) with hCA
  set πA : CA ⟶ Spec (CommRingCat.of A) := pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A) with hπA
  set g' : CA ⟶ pullback c t := pullback.map c (Scheme.TwoAffineOpenCover.specMap R A) c t (𝟙 C) j (𝟙 _)
    (by simp) (by rw [Category.comp_id, hj]) with hg'
  have hg'fst : g' ≫ pullback.fst c t = pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A) := by
    rw [hg', pullback.lift_fst, Category.comp_id]
  have hg'snd : g' ≫ pullback.snd c t = πA ≫ j := by
    rw [hg', pullback.lift_snd]
  have hcart : IsPullback g' πA (pullback.snd c t) j := by
    refine IsPullback.of_right ?_ hg'snd (IsPullback.of_hasPullback c t)
    rw [hg'fst, hj]
    exact IsPullback.of_hasPullback c (Scheme.TwoAffineOpenCover.specMap R A)
  haveI : IsProper πA := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  haveI : Flat πA := MorphismProperty.pullback_snd (P := @Flat) _ _ inferInstance
  let 𝒱 : CA.TwoAffineOpenCover := 𝔉.twoAffineOpenCover.pullback c A

  let h0 : (pullback c t).Modules → PrimeSpectrum A → ℕ := fun M 𝔭 =>
    Module.finrank 𝔭.asIdeal.ResidueField
      (LinearMap.ker ((𝒱.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).cechDiff.baseChange
        𝔭.asIdeal.ResidueField))
  have hVclosed : IsClosed {𝔭 : PrimeSpectrum A | 1 ≤ h0 L.L 𝔭} :=
    isClosed_setOf_le_finrank_ker_cechDiff_baseChange πA 𝒱 _ (L.isInvertible.pullback g') 1

  have geom : ∀ 𝔭 : PrimeSpectrum A, ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (sb : Spec (CommRingCat.of K) ⟶ T),
      sb.base (IsLocalRing.closedPoint K) = j.base 𝔭 := by
    intro 𝔭
    refine ⟨AlgebraicClosure 𝔭.asIdeal.ResidueField, inferInstance, inferInstance,
      Scheme.TwoAffineOpenCover.specMap 𝔭.asIdeal.ResidueField (AlgebraicClosure 𝔭.asIdeal.ResidueField) ≫
        Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField ≫ j, ?_⟩
    change j.base ((Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField).base
      ((Scheme.TwoAffineOpenCover.specMap 𝔭.asIdeal.ResidueField (AlgebraicClosure 𝔭.asIdeal.ResidueField)).base
        (IsLocalRing.closedPoint _))) = j.base 𝔭
    rw [specMap_residueField_base]

  have hO1 : ∀ 𝔭 : PrimeSpectrum A, h0 (𝟙_ (pullback c t).Modules) 𝔭 = 1 := by
    intro 𝔭
    obtain ⟨K, _, _, sb, hsb⟩ := geom 𝔭
    obtain ⟨𝒲, h𝒲⟩ :=
      exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField c t j πA g' hcart 𝒱 𝔭 sb hsb
    obtain ⟨hO0, -⟩ := h𝒲 (𝟙_ (pullback c t).Modules) (Scheme.Modules.isInvertible_unit _)
    change Module.finrank _ _ = 1
    rw [← hO0]
    exact finrank_H0_fibreModule_unit_eq_one c t K sb 𝒲

  have key : ∀ 𝔭 : PrimeSpectrum A,
      (∃ (k : Type u) (_ : Field k) (s : Spec (CommRingCat.of k) ⟶ T),
        s.base (IsLocalRing.closedPoint k) = j.base 𝔭 ∧
          Nonempty (fibreModule c t s L.L ≅ 𝟙_ (pullback (pullback.snd c t) s).Modules)) ↔ 1 ≤ h0 L.L 𝔭 := by
    intro 𝔭
    constructor
    · rintro ⟨k, _, s, hs, ⟨e⟩⟩
      obtain ⟨𝒲, h𝒲⟩ :=
        exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField c t j πA g' hcart 𝒱 𝔭 s hs
      obtain ⟨hL0, -⟩ := h𝒲 L.L L.isInvertible
      obtain ⟨hO0, -⟩ := h𝒲 (𝟙_ (pullback c t).Modules) (Scheme.Modules.isInvertible_unit _)
      have hcongr := finrank_H0_congr (fibreAt c t s) 𝒲
        (e ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso (pullback.fst (pullback.snd c t) s)).symm)
      rw [← hO1 𝔭]
      change Module.finrank _ _ ≤ Module.finrank _ _
      rw [← hL0, ← hO0, hcongr]
    · intro h
      obtain ⟨K, _, _, sb, hsb⟩ := geom 𝔭
      obtain ⟨𝒲, h𝒲⟩ :=
        exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField c t j πA g' hcart 𝒱 𝔭 sb hsb
      obtain ⟨hL0, -⟩ := h𝒲 L.L L.isInvertible
      refine ⟨K, inferInstance, sb, hsb, pointwise sb 𝒲 ?_⟩
      rw [hL0]
      exact h
  refine ⟨j.base '' {𝔭 : PrimeSpectrum A | 1 ≤ h0 L.L 𝔭}ᶜ, ?_, j.isOpenEmbedding.isOpenMap _ hVclosed.isOpen_compl, ?_⟩
  ·
    rintro _ ⟨𝔭, h𝔭, rfl⟩ hmem
    exact h𝔭 ((key 𝔭).mp hmem)
  ·
    have hxr : x ∈ Set.range ⇑j.base := by
      rw [hjdef]
      change x ∈ Set.range hW.fromSpec
      rw [hW.range_fromSpec]; exact hxW
    obtain ⟨𝔭, rfl⟩ := hxr
    exact ⟨𝔭, fun h𝔭 => hx ((key 𝔭).mpr h𝔭), rfl⟩
