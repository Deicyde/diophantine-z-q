/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_CategoryTheory_OverTotalPresheaf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_AffineLimit
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_FGSubalgebra
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_FGSubalgebra_nonempty_isLimit_specCone
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_iff_eulerChar_sectionsOf_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_isLFPSurj_relPicardPresheaf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_isOpen_setOf_isAlgEquivZero_fibre
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
-- Original source-local namespace open deferred until after its declaration.
open AlgebraicGeometry.RelPicard
-- Original source-local namespace open deferred until after its declaration.
open NeronModelInfra
open AlgebraicGeometry.AffineLimit

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Spec.map_comp Spec.map_preimage SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral exists_map_eq_top LocallyOfFiniteType GeometricallyIntegral.isIntegral_of_subsingleton Spec IsIntegral Spec.map Scheme smoothOfRelativeDimension_isStableUnderBaseChange Spec.preimage HasRingHomProperty.Spec_iff Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules HasRingHomProperty geometrically Scheme.Modules.pullbackComp Scheme.Hom.id_preimage Scheme.Modules.pullbackUnitIso Scheme.Modules.isInvertible_unitFLT SmoothProperCurve.FiniteMapData Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap AffineLimit.IsLFPSurj FGSubalgebra FGSubalgebra.specDiagram FGSubalgebra.specCone FGSubalgebra.nonempty_isLimit_specCone Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso)
namespace RelPicard
export _root_.AlgebraicGeometry.RelPicard (baseChangeSnd RigidifiedLineBundle relPicardPresheaf fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso FibrewiseAlgEquivZero.pullback algEquivZeroCut relSubPicPresheaf fibreModule isAlgEquivZero_iff_eulerChar_sectionsOf_eq exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq isLFPSurj_relPicardPresheaf isOpen_setOf_isAlgEquivZero_fibre)
namespace LfpPicSurj
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry

variable {R : Type u} [CommRing R]

theorem twoAffineOpenCover_ext {X : Scheme.{u}} {𝒱 𝒲 : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒲.U0) (h1 : 𝒱.U1 = 𝒲.U1) : 𝒱 = 𝒲 := by
  obtain ⟨U0, U1, p1, p2, p3, p4⟩ := 𝒱
  obtain ⟨U0', U1', q1, q2, q3, q4⟩ := 𝒲
  change U0 = U0' at h0
  change U1 = U1' at h1
  subst h0
  subst h1
  rfl

theorem finrank_sectionsOf_eq_of_iso {S : Type u} [CommRing S] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of S))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Module.finrank S (𝒱.sectionsOf x M).H0 = Module.finrank S (𝒱.sectionsOf x M').H0 ∧
      Module.finrank S (𝒱.sectionsOf x M).H1 = Module.finrank S (𝒱.sectionsOf x M').H1 := by
  obtain ⟨𝒱', hU0, hU1, ⟨e0⟩, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X)
    (Category.id_comp x) 𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  have h𝒱 : 𝒱' = 𝒱 := twoAffineOpenCover_ext (hU0.trans (Scheme.Hom.id_preimage _)) (hU1.trans (Scheme.Hom.id_preimage _))
  subst h𝒱
  exact ⟨e0.finrank_eq, e1.finrank_eq⟩

lemma locallyOfFiniteType_Spec_algebraMap (A₀ : Type u) [CommRing A₀] [Algebra R A₀] [Algebra.FiniteType R A₀] :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), CommRingCat.hom_ofHom]
  exact RingHom.finiteType_algebraMap.mpr ‹_›

lemma specOverOfSubalgebra_comp_specOverOfLE {A : Type u} [CommRing A] [Algebra R A] (A₀ A₁ : Subalgebra R A)
    (h : A₀ ≤ A₁) : specOverOfSubalgebra R A₁ ≫ specOverOfLE R A₀ A₁ h = specOverOfSubalgebra R A₀ := by
  ext : 1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

lemma exists_geometricPoint (A : Type u) [CommRing A] (P : Spec (CommRingCat.of A)) :
    ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k) (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
      Set.range ⇑s ⊆ {P} := by
  refine ⟨AlgebraicClosure P.asIdeal.ResidueField, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom ((algebraMap P.asIdeal.ResidueField (AlgebraicClosure P.asIdeal.ResidueField)).comp
      (algebraMap A P.asIdeal.ResidueField))), ?_⟩
  rintro _ ⟨p, rfl⟩
  obtain rfl : p = IsLocalRing.closedPoint _ := Subsingleton.elim _ _
  rw [Set.mem_singleton_iff]
  apply PrimeSpectrum.ext
  change Ideal.comap _ (IsLocalRing.maximalIdeal _) = P.asIdeal
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, CommRingCat.hom_ofHom, ← RingHom.comap_ker,
    (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap P.asIdeal.ResidueField _).injective,
    ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

theorem exists_algebra_eq_specMap_comp_specMap {A : Type u} [CommRing A] (𝔭 : PrimeSpectrum A) {k : Type u} [Field k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)) (hs : s (IsLocalRing.closedPoint k) = 𝔭) :
    ∃ (_ : Algebra 𝔭.asIdeal.ResidueField k),
      s = Scheme.TwoAffineOpenCover.specMap 𝔭.asIdeal.ResidueField k ≫
        Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField := by
  obtain ⟨φ, rfl⟩ : ∃ φ : A →+* k, Spec.map (CommRingCat.ofHom φ) = s :=
    ⟨(Spec.preimage s).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  have hker : 𝔭.asIdeal = RingHom.ker φ := by
    rw [← hs]
    change Ideal.comap φ (IsLocalRing.maximalIdeal k) = RingHom.ker φ
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  have hunit : 𝔭.asIdeal.primeCompl ≤ Submonoid.comap φ (IsUnit.submonoid k) := fun a ha => by
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    exact fun h0 => ha (show a ∈ 𝔭.asIdeal by rw [hker]; exact RingHom.mem_ker.mpr h0)
  let ψ : 𝔭.asIdeal.ResidueField →+* k := Ideal.ResidueField.lift 𝔭.asIdeal φ hker.le hunit
  letI : Algebra 𝔭.asIdeal.ResidueField k := ψ.toAlgebra
  have hcomp : (algebraMap 𝔭.asIdeal.ResidueField k).comp (algebraMap A 𝔭.asIdeal.ResidueField) = φ := by
    ext a
    exact Ideal.ResidueField.lift_algebraMap 𝔭.asIdeal φ hker.le hunit a
  refine ⟨ψ.toAlgebra, ?_⟩
  rw [Scheme.TwoAffineOpenCover.specMap, Scheme.TwoAffineOpenCover.specMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, hcomp]

variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

theorem isAlgEquivZero_fibre_pullbackAlong {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε t)
    {k : Type u} [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')
    (h : IsAlgEquivZero (fibreAt c t (s' ≫ ψ.1)) (fibreModule c t (s' ≫ ψ.1) M.L)) :
    IsAlgEquivZero (fibreAt c t' s') (fibreModule c t' s' (M.pullbackAlong ψ).L) := by
  have hψ : pullback.snd c t' ≫ ψ.1 = baseChangeSnd c ψ ≫ pullback.snd c t := by
    simp only [baseChangeSnd, pullback.lift_snd]
  let e : Limits.pullback (pullback.snd c t') s' ⟶ Limits.pullback (pullback.snd c t) (s' ≫ ψ.1) :=
    pullback.map _ _ _ _ (baseChangeSnd c ψ) (𝟙 _) ψ.1 hψ (by simp)
  have he : e ≫ fibreAt c t (s' ≫ ψ.1) = fibreAt c t' s' := by
    simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : e ≫ pullback.fst (pullback.snd c t) (s' ≫ ψ.1) =
      pullback.fst (pullback.snd c t') s' ≫ baseChangeSnd c ψ := by
    simp only [e, pullback.lift_fst]
  refine IsAlgEquivZero.of_iso ?_ (h.pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm

theorem isAlgEquivZero_fibre_of_pullbackAlong {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε t)
    {k : Type u} [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')
    (h : IsAlgEquivZero (fibreAt c t' s') (fibreModule c t' s' (M.pullbackAlong ψ).L)) :
    IsAlgEquivZero (fibreAt c t (s' ≫ ψ.1)) (fibreModule c t (s' ≫ ψ.1) M.L) := by

  have hbc : IsPullback (baseChangeSnd c ψ) (pullback.snd c t') (pullback.snd c t) ψ.1 := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback c t)
    rw [show baseChangeSnd c ψ ≫ pullback.fst c t = pullback.fst c t' from
      (pullback.lift_fst _ _ _).trans (Category.comp_id _), ψ.2]
    exact IsPullback.of_hasPullback c t'

  have hP : IsPullback (pullback.fst (pullback.snd c t') s' ≫ baseChangeSnd c ψ) (pullback.snd (pullback.snd c t') s')
      (pullback.snd c t) (s' ≫ ψ.1) :=
    (IsPullback.of_hasPullback (pullback.snd c t') s').paste_horiz hbc
  let e := hP.isoPullback.inv
  have he : e ≫ fibreAt c t' s' = fibreAt c t (s' ≫ ψ.1) := hP.isoPullback_inv_snd
  refine IsAlgEquivZero.of_iso ?_ (h.pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (by rw [Category.assoc]; exact hP.isoPullback_inv_fst)).app M.L

theorem isAlgEquivZero_fibre_of_isAlgEquivZero_fibre [IsNoetherianRing R] [IsProper c] [SmoothOfRelativeDimension 1 c]
    [GeometricallyIntegral c] (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (A₀ : Type u) [CommRing A₀] [Algebra R A₀] [Algebra.FiniteType R A₀]
    (L : RigidifiedLineBundle c ε (Spec.map (CommRingCat.ofHom (algebraMap R A₀))))
    (P : Spec (CommRingCat.of A₀))
    {k₁ : Type u} [Field k₁] [IsAlgClosed k₁] (s₁ : Spec (CommRingCat.of k₁) ⟶ Spec (CommRingCat.of A₀))
    (hs₁ : Set.range ⇑s₁ ⊆ {P})
    (h₁ : IsAlgEquivZero (fibreAt c _ s₁) (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) s₁ L.L))
    {k₂ : Type u} [Field k₂] [IsAlgClosed k₂] (s₂ : Spec (CommRingCat.of k₂) ⟶ Spec (CommRingCat.of A₀))
    (hs₂ : Set.range ⇑s₂ ⊆ {P}) :
    IsAlgEquivZero (fibreAt c _ s₂) (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) s₂ L.L) := by

  obtain ⟨_, rfl⟩ := exists_algebra_eq_specMap_comp_specMap (A := A₀) P s₁ (hs₁ ⟨_, rfl⟩)
  obtain ⟨_, rfl⟩ := exists_algebra_eq_specMap_comp_specMap (A := A₀) P s₂ (hs₂ ⟨_, rfl⟩)

  obtain ⟨𝔉, -⟩ := h𝔉 0
  letI : Algebra R P.asIdeal.ResidueField := ((algebraMap A₀ P.asIdeal.ResidueField).comp (algebraMap R A₀)).toAlgebra
  have hRκ : Scheme.TwoAffineOpenCover.specMap R P.asIdeal.ResidueField ≫ 𝟙 _ =
      Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField ≫ Spec.map (CommRingCat.ofHom (algebraMap R A₀)) := by
    rw [Category.comp_id, Scheme.TwoAffineOpenCover.specMap, Scheme.TwoAffineOpenCover.specMap, ← Spec.map_comp]
    rfl
  let g' : pullback c (Scheme.TwoAffineOpenCover.specMap R P.asIdeal.ResidueField) ⟶
      pullback c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) :=
    pullback.map _ _ _ _ (𝟙 C) (Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField) (𝟙 _) (by simp) hRκ
  have hcart : IsPullback g' (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R P.asIdeal.ResidueField))
      (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))))
      (Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback c _)
    rw [show g' ≫ pullback.fst c _ = pullback.fst c _ from (pullback.lift_fst _ _ _).trans (Category.comp_id _),
      ← Category.comp_id (Scheme.TwoAffineOpenCover.specMap R P.asIdeal.ResidueField), hRκ]
    exact IsPullback.of_hasPullback c _
  obtain ⟨𝒲₀, -, -⟩ := exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback c
    (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) L.L (Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField)
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R P.asIdeal.ResidueField)) g' hcart
    ((Scheme.Modules.pullback g').obj L.L) (Iso.refl _)
    (𝔉.twoAffineOpenCover.pullback c P.asIdeal.ResidueField)

  obtain ⟨𝒲₁, h𝒲₁⟩ := exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq c
    (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) (Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField) 𝒲₀ k₁
  obtain ⟨𝒲₂, h𝒲₂⟩ := exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq c
    (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) (Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField) 𝒲₀ k₂
  obtain ⟨hL0₁, hL1₁⟩ := h𝒲₁ L.L L.isInvertible
  obtain ⟨hO0₁, hO1₁⟩ := h𝒲₁ (SheafOfModules.unit (pullback c (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))).ringCatSheaf) (Scheme.Modules.isInvertible_unitFLT _)
  obtain ⟨hL0₂, hL1₂⟩ := h𝒲₂ L.L L.isInvertible
  obtain ⟨hO0₂, hO1₂⟩ := h𝒲₂ (SheafOfModules.unit (pullback c (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))).ringCatSheaf) (Scheme.Modules.isInvertible_unitFLT _)

  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI hsm : SmoothOfRelativeDimension 1 (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  have inst : ∀ {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A₀)),
      IsProper (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) s) ∧
      SmoothOfRelativeDimension 1 (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) s) ∧
      IsIntegral (pullback (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))) s) := by
    intro k _ s
    haveI : GeometricallyIntegral (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) s) := by
      unfold fibreAt; infer_instance
    refine ⟨by unfold fibreAt; infer_instance,
      by unfold fibreAt; exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ hsm, ?_⟩
    exact GeometricallyIntegral.isIntegral_of_subsingleton (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) s)
  obtain ⟨hp₁, hs₁', hi₁⟩ := inst (Scheme.TwoAffineOpenCover.specMap P.asIdeal.ResidueField k₁ ≫
    Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField)
  obtain ⟨hp₂, hs₂', hi₂⟩ := inst (Scheme.TwoAffineOpenCover.specMap P.asIdeal.ResidueField k₂ ≫
    Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField)

  have hu₁ := finrank_sectionsOf_eq_of_iso (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) (Scheme.TwoAffineOpenCover.specMap P.asIdeal.ResidueField k₁ ≫ Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField)) 𝒲₁
    (M := fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) (Scheme.TwoAffineOpenCover.specMap P.asIdeal.ResidueField k₁ ≫ Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField) (SheafOfModules.unit (pullback c (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))).ringCatSheaf))
    (Scheme.Modules.pullbackUnitIso _)
  have hu₂ := finrank_sectionsOf_eq_of_iso (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) (Scheme.TwoAffineOpenCover.specMap P.asIdeal.ResidueField k₂ ≫ Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField)) 𝒲₂
    (M := fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) (Scheme.TwoAffineOpenCover.specMap P.asIdeal.ResidueField k₂ ≫ Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField) (SheafOfModules.unit (pullback c (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))).ringCatSheaf))
    (Scheme.Modules.pullbackUnitIso _)
  obtain ⟨hu0₁, hu1₁⟩ := hu₁
  obtain ⟨hu0₂, hu1₂⟩ := hu₂
  have hχ₁ := (isAlgEquivZero_iff_eulerChar_sectionsOf_eq k₁ (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) (Scheme.TwoAffineOpenCover.specMap P.asIdeal.ResidueField k₁ ≫ Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField))
    (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) (Scheme.TwoAffineOpenCover.specMap P.asIdeal.ResidueField k₁ ≫ Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField) L.L) (L.isInvertible.pullback _) 𝒲₁).mp h₁
  refine (isAlgEquivZero_iff_eulerChar_sectionsOf_eq k₂ (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) (Scheme.TwoAffineOpenCover.specMap P.asIdeal.ResidueField k₂ ≫ Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField))
    (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) (Scheme.TwoAffineOpenCover.specMap P.asIdeal.ResidueField k₂ ≫ Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField) L.L) (L.isInvertible.pullback _) 𝒲₂).mpr ?_
  omega

theorem exists_fg_preimage_eq_top {A : Type u} [CommRing A] [Algebra R A] (A₀ : Subalgebra R A) (hA₀ : A₀.FG)
    (W : (Spec (CommRingCat.of ↥A₀)).Opens) (hW : Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ⁻¹ᵁ W = ⊤) :
    ∃ (A₁ : Subalgebra R A) (_ : A₁.FG) (hle : A₀ ≤ A₁),
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom) ⁻¹ᵁ W = ⊤ := by
  obtain ⟨hc⟩ := FGSubalgebra.nonempty_isLimit_specCone R A
  obtain ⟨j, f, hf⟩ := exists_map_eq_top (FGSubalgebra.specDiagram R A) (FGSubalgebra.specCone R A) hc
    (i := op ⟨A₀, hA₀⟩) W hW
  exact ⟨j.unop.1, j.unop.2, f.unop.le, hf⟩

end AlgebraicGeometry.RelPicard.LfpPicSurj
open _root_.P2MW.S_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut.AlgebraicGeometry
open _root_.P2MW.S_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut.AlgebraicGeometry.RelPicard

open AlgebraicGeometry.RelPicard.LfpPicSurj in

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m) :
    IsLFPSurj (relSubPicPresheaf c ε (algEquivZeroCut c ε)) := by
  classical
  intro A _ _ x
  obtain ⟨𝔉, -⟩ := h𝔉 0

  obtain ⟨A₀, hA₀, y₀, hy₀⟩ := isLFPSurj_relPicardPresheaf R 𝔉.twoAffineOpenCover c ε A x.1
  obtain ⟨L₀, rfl⟩ := Quotient.exists_rep y₀
  haveI : Algebra.FiniteType R ↥A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hA₀
  haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R ↥A₀))) :=
    locallyOfFiniteType_Spec_algebraMap ↥A₀
  haveI : LocallyOfFiniteType (unop (op (specOver R ↥A₀))).hom := locallyOfFiniteType_Spec_algebraMap ↥A₀

  have hx2 : FibrewiseAlgEquivZero (L₀.pullbackAlong ⟨(specOverOfSubalgebra R A₀).left, Over.w _⟩) := by
    have h2 := x.2
    rw [← hy₀] at h2
    exact h2

  let W : (Spec (CommRingCat.of ↥A₀)).Opens :=
    ⟨{P | ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ↥A₀)),
        Set.range ⇑s ⊆ {P} → IsAlgEquivZero (fibreAt c _ s)
          (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R ↥A₀))) s L₀.L)},
      isOpen_setOf_isAlgEquivZero_fibre R c ε h𝔉 _ L₀⟩

  have himg : Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ⁻¹ᵁ W = ⊤ := by
    refine top_le_iff.mp fun Q _ => ?_
    obtain ⟨k, _, _, s, hs⟩ := exists_geometricPoint A Q
    intro k' _ _ s' hs'
    refine isAlgEquivZero_fibre_of_isAlgEquivZero_fibre c ε h𝔉 ↥A₀ L₀ _
      (s ≫ Spec.map (CommRingCat.ofHom A₀.val.toRingHom)) ?_ ?_ s' hs'
    · rintro _ ⟨p, rfl⟩
      exact congrArg (Spec.map (CommRingCat.ofHom A₀.val.toRingHom)) (hs ⟨p, rfl⟩)
    · exact isAlgEquivZero_fibre_of_pullbackAlong c ε ⟨(specOverOfSubalgebra R A₀).left, Over.w _⟩ L₀ s (hx2 k s)

  obtain ⟨A₁, hA₁, hle, hW⟩ := exists_fg_preimage_eq_top A₀ hA₀ W himg

  refine ⟨A₁, hA₁, ⟨(relPicardPresheaf c ε).map (specOverOfLE R A₀ A₁ hle).op (Quotient.mk _ L₀), ?_⟩, ?_⟩
  · show FibrewiseAlgEquivZero (L₀.pullbackAlong ⟨(specOverOfLE R A₀ A₁ hle).left, Over.w _⟩)
    intro k _ _ s₁
    have hP : (specOverOfLE R A₀ A₁ hle).left (s₁ (IsLocalRing.closedPoint k)) ∈ W := by
      have : s₁ (IsLocalRing.closedPoint k) ∈ (⊤ : (Spec (CommRingCat.of ↥A₁)).Opens) := trivial
      rwa [← hW] at this
    refine isAlgEquivZero_fibre_pullbackAlong c ε _ L₀ s₁ (hP k (s₁ ≫ (specOverOfLE R A₀ A₁ hle).left) ?_)
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rfl
  · apply Subtype.ext
    change (relPicardPresheaf c ε).map (specOverOfSubalgebra R A₁).op
        ((relPicardPresheaf c ε).map (specOverOfLE R A₀ A₁ hle).op (Quotient.mk _ L₀)) = x.1
    rw [← types_comp_apply _ ((relPicardPresheaf c ε).map _), ← Functor.map_comp, ← op_comp,
      specOverOfSubalgebra_comp_specOverOfLE]
    exact hy₀
