/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_isSeparated_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_isClosed_setOf_exists_fibreModule_iso_unit
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isSeparated_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_RelPicard_isSeparated_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData.AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open P2MW.S_AlgebraicGeometry_RelPicard_isSeparated_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData.AlgebraicGeometry.RelPicard
open NeronModelInfra
open GoodReductionJacobian
open AlgebraicCurve
open CategoryTheory.MonoidalCategory
open Opposite

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (SmoothOfRelativeDimension IsClosedImmersion.of_isPreimmersion IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral LocallyOfFiniteType Spec Scheme IsClosedImmersion IsSeparated Scheme.Modules.pullbackCongr Scheme.fromSpecResidueField_apply Scheme.Modules.pullbackId Scheme.Modules Scheme.Hom.comp_apply geometrically Scheme.Modules.pullbackComp Scheme.Modules.pullbackUnitIso SmoothProperCurve.FiniteMapData Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso)
namespace RelPicard
export _root_.AlgebraicGeometry.RelPicard (baseChangeSnd RigidifiedLineBundle RigidifiedLineBundle.unit RepresentsRelSubPic FibrewiseAlgEquivZero FibrewiseAlgEquivZero.pullback algEquivZeroCut fibreModule FibrewiseAlgEquivZero.of_tensor_iso_unit isClosed_setOf_exists_fibreModule_iso_unit)
namespace Sep
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

noncomputable def isoOfTensorIsoUnit {V : Scheme.{u}} (X Y Y' : V.Modules) (i : X ⊗ Y ≅ 𝟙_ _) (i' : X ⊗ Y' ≅ 𝟙_ _) : Y ≅ Y' :=
  (λ_ Y).symm ≪≫ (i'.symm ⊗ᵢ Iso.refl Y) ≪≫ ((β_ X Y') ⊗ᵢ Iso.refl Y) ≪≫ α_ Y' X Y ≪≫
    (Iso.refl Y' ⊗ᵢ i) ≪≫ ρ_ Y'

noncomputable def isoUnitOfPullbackIso {X Y : Scheme.{u}} (φ : X ≅ Y) (M : Y.Modules)
    (e : (Scheme.Modules.pullback φ.hom).obj M ≅ 𝟙_ X.Modules) : M ≅ 𝟙_ Y.Modules :=
  ((Scheme.Modules.pullbackId Y).app M).symm ≪≫
    (Scheme.Modules.pullbackCongr φ.inv_hom_id.symm).app M ≪≫
    (Scheme.Modules.pullbackComp φ.inv φ.hom).symm.app M ≪≫
    (Scheme.Modules.pullback φ.inv).mapIso e ≪≫ Scheme.Modules.pullbackTensorUnitObjIso φ.inv

theorem nonempty_fibreModule_iso_unit_iff {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (Q : RigidifiedLineBundle c ε (pullback.fst D.toBase D.toBase ≫ D.toBase))
    (hQ : Nonempty ((((h.poincare.pullbackAlong ⟨pullback.snd D.toBase D.toBase, pullback.condition.symm⟩).tensor Q).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) (pullback.fst D.toBase D.toBase ≫ D.toBase)).L)))
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ pullback D.toBase D.toBase) :
    Nonempty (fibreModule c (pullback.fst D.toBase D.toBase ≫ D.toBase) s
        ((h.poincare.pullbackAlong ⟨pullback.fst D.toBase D.toBase, rfl⟩).tensor Q).L ≅ 𝟙_ _) ↔
      s ≫ pullback.fst D.toBase D.toBase = s ≫ pullback.snd D.toBase D.toBase := by

  let T := pullback D.toBase D.toBase
  let t : T ⟶ Spec (CommRingCat.of R) := pullback.fst D.toBase D.toBase ≫ D.toBase
  let P₁ : RigidifiedLineBundle c ε t := h.poincare.pullbackAlong ⟨pullback.fst D.toBase D.toBase, rfl⟩
  let P₂ : RigidifiedLineBundle c ε t :=
    h.poincare.pullbackAlong ⟨pullback.snd D.toBase D.toBase, pullback.condition.symm⟩
  let ψ : SchemeHomOver (s ≫ t) t := ⟨s, rfl⟩
  let g₁ : SchemeHomOver (s ≫ t) D.toBase := ⟨s ≫ pullback.fst D.toBase D.toBase, by rw [Category.assoc]⟩
  let g₂ : SchemeHomOver (s ≫ t) D.toBase := ⟨s ≫ pullback.snd D.toBase D.toBase, by
    rw [Category.assoc, ← pullback.condition]⟩

  have hbc : IsPullback (baseChangeSnd c ψ) (pullback.snd c (s ≫ t)) (pullback.snd c t) s := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback c t)
    rw [show baseChangeSnd c ψ ≫ pullback.fst c t = pullback.fst c (s ≫ t) from
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)]
    exact IsPullback.of_hasPullback c (s ≫ t)
  let φ : pullback c (s ≫ t) ≅ pullback (pullback.snd c t) s := hbc.isoPullback
  have hφ : φ.hom ≫ pullback.fst (pullback.snd c t) s = baseChangeSnd c ψ := hbc.isoPullback_hom_fst

  have Φ : ∀ (N : RigidifiedLineBundle c ε t),
      (Scheme.Modules.pullback φ.hom).obj (fibreModule c t s N.L) ≅ (N.pullbackAlong ψ).L := fun N =>
    (Scheme.Modules.pullbackComp _ _).app N.L ≪≫ (Scheme.Modules.pullbackCongr hφ).app N.L

  have e₁ : (P₁.pullbackAlong ψ).L ≅ (h.poincare.pullbackAlong g₁).L :=
    h.poincare.pullbackAlongPullbackAlongIso ⟨pullback.fst D.toBase D.toBase, rfl⟩ ψ
  have e₂ : (P₂.pullbackAlong ψ).L ≅ (h.poincare.pullbackAlong g₂).L :=
    h.poincare.pullbackAlongPullbackAlongIso ⟨pullback.snd D.toBase D.toBase, pullback.condition.symm⟩ ψ
  have iQ : (P₂.pullbackAlong ψ).L ⊗ (Q.pullbackAlong ψ).L ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫ (Scheme.Modules.pullback _).mapIso hQ.some ≪≫
      Scheme.Modules.pullbackUnitIso _
  constructor
  · rintro ⟨e⟩

    have e' : (P₁.pullbackAlong ψ).L ⊗ (Q.pullbackAlong ψ).L ≅ 𝟙_ _ :=
      (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫ (Φ (P₁.tensor Q)).symm ≪≫
        (Scheme.Modules.pullback φ.hom).mapIso e ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _

    have i12 : (P₁.pullbackAlong ψ).L ≅ (P₂.pullbackAlong ψ).L :=
      isoOfTensorIsoUnit _ _ _ ((β_ _ _) ≪≫ e') ((β_ _ _) ≪≫ iQ)
    have hg : g₁ = g₂ := h.ext_of_iso (s ≫ t) g₁ g₂ ⟨e₁.symm ≪≫ i12 ≪≫ e₂⟩
    exact congrArg Subtype.val hg
  · intro hs
    have hg : g₁ = g₂ := Subtype.ext hs
    have i12 : (P₁.pullbackAlong ψ).L ≅ (P₂.pullbackAlong ψ).L :=
      e₁ ≪≫ eqToIso (by rw [hg]) ≪≫ e₂.symm
    have e' : (P₁.pullbackAlong ψ).L ⊗ (Q.pullbackAlong ψ).L ≅ 𝟙_ _ := (i12 ⊗ᵢ Iso.refl _) ≪≫ iQ
    exact ⟨isoUnitOfPullbackIso φ _ ((Φ (P₁.tensor Q)) ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ e')⟩

end AlgebraicGeometry.RelPicard.Sep

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [LocallyOfFiniteType D.toBase] :
    IsSeparated D.toBase := by

  let T := pullback D.toBase D.toBase
  let t : T ⟶ Spec (CommRingCat.of R) := pullback.fst D.toBase D.toBase ≫ D.toBase
  let P₁ : RigidifiedLineBundle c ε t := h.poincare.pullbackAlong ⟨pullback.fst D.toBase D.toBase, rfl⟩
  let P₂ : RigidifiedLineBundle c ε t := h.poincare.pullbackAlong ⟨pullback.snd D.toBase D.toBase, pullback.condition.symm⟩
  obtain ⟨Q, hQ⟩ := P₂.exists_tensor_iso_unit
  have hP₁ : FibrewiseAlgEquivZero P₁ := FibrewiseAlgEquivZero.pullback _ h.poincare_mem
  have hP₂ : FibrewiseAlgEquivZero P₂ := FibrewiseAlgEquivZero.pullback _ h.poincare_mem
  have hL : FibrewiseAlgEquivZero (P₁.tensor Q) := hP₁.tensor (FibrewiseAlgEquivZero.of_tensor_iso_unit hQ hP₂)
  haveI : LocallyOfFiniteType t := inferInstance
  have hZ := isClosed_setOf_exists_fibreModule_iso_unit R c ε h𝔉 t (P₁.tensor Q) hL

  have hrange : Set.range ⇑(pullback.diagonal D.toBase) = {x : T | ∃ (k : Type u) (_ : Field k)
      (s : Spec (CommRingCat.of k) ⟶ T), s.base (IsLocalRing.closedPoint k) = x ∧
        Nonempty (fibreModule c t s (P₁.tensor Q).L ≅ 𝟙_ (pullback (pullback.snd c t) s).Modules)} := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      refine ⟨D.P.residueField q, inferInstance, D.P.fromSpecResidueField q ≫ pullback.diagonal D.toBase, ?_, ?_⟩
      · change (D.P.fromSpecResidueField q ≫ pullback.diagonal D.toBase) (IsLocalRing.closedPoint _) = _
        rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
      · exact (Sep.nonempty_fibreModule_iso_unit_iff h Q hQ _).mpr (by simp)
    · rintro ⟨k, _, s, rfl, hs⟩
      have heq := (Sep.nonempty_fibreModule_iso_unit_iff h Q hQ s).mp hs
      have hfac : (s ≫ pullback.fst D.toBase D.toBase) ≫ pullback.diagonal D.toBase = s := by
        apply pullback.hom_ext <;> simp [heq]
      exact ⟨(s ≫ pullback.fst D.toBase D.toBase) (IsLocalRing.closedPoint k), by
        rw [← Scheme.Hom.comp_apply, hfac]⟩
  rw [← hrange] at hZ
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hZ⟩
