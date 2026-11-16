/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_isOpen_setOf_isAlgEquivZero_fibre. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_iff_eulerChar_sectionsOf_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isLocallyConstant_finrank_ker_sub_finrank_coker_cechDiff_baseChange
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isOpen_setOf_isAlgEquivZero_fibre

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open NeronModelInfra
open TensorProduct

noncomputable section

namespace Pic0Locus

theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

theorem finrank_H0_H1_congr {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Module.finrank k (𝒱.sectionsOf x M).H0 = Module.finrank k (𝒱.sectionsOf x M').H0 ∧
      Module.finrank k (𝒱.sectionsOf x M).H1 = Module.finrank k (𝒱.sectionsOf x M').H1 := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X) (Category.id_comp x)
      𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain rfl : 𝒱₂ = 𝒱 := cover_ext h0 h1
  exact ⟨e0.finrank_eq, e1.finrank_eq⟩

theorem specMap_residueField_base {A : Type u} [CommRing A] (𝔭 : PrimeSpectrum A) (p : Spec (CommRingCat.of 𝔭.asIdeal.ResidueField)) :
    (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField).base p = 𝔭 := by
  apply PrimeSpectrum.ext
  have hp : p.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right p.isPrime.ne_top
  change Ideal.comap (algebraMap A 𝔭.asIdeal.ResidueField) p.asIdeal = 𝔭.asIdeal
  rw [hp, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

end Pic0Locus

open Pic0Locus in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem Pic0Locus.main
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t] (L : RigidifiedLineBundle c ε t) :
    IsOpen {x : T | ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      Set.range ⇑s ⊆ {x} → IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L)} := by
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

  have chi_unit : ∀ {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H0 =
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s)
          (SheafOfModules.unit (pullback (pullback.snd c t) s).ringCatSheaf : (pullback (pullback.snd c t) s).Modules)).H0 ∧
      Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H1 =
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s)
          (SheafOfModules.unit (pullback (pullback.snd c t) s).ringCatSheaf : (pullback (pullback.snd c t) s).Modules)).H1 :=
    fun s 𝒲 => finrank_H0_H1_congr (fibreAt c t s) 𝒲
      (Scheme.Modules.pullbackTensorUnitObjIso (pullback.fst (pullback.snd c t) s))
  rw [isOpen_iff_forall_mem_open]
  intro x hx

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

  let d : (pullback c t).Modules → PrimeSpectrum A → ℤ := fun M 𝔭 =>
    (Module.finrank 𝔭.asIdeal.ResidueField
        (LinearMap.ker ((𝒱.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).cechDiff.baseChange
          𝔭.asIdeal.ResidueField)) : ℤ) -
      Module.finrank 𝔭.asIdeal.ResidueField
        ((𝔭.asIdeal.ResidueField ⊗[A] (𝒱.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).M01) ⧸
          LinearMap.range ((𝒱.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).cechDiff.baseChange
            𝔭.asIdeal.ResidueField))
  have hdL : IsLocallyConstant (d L.L) :=
    Scheme.TwoAffineOpenCover.isLocallyConstant_finrank_ker_sub_finrank_coker_cechDiff_baseChange πA 𝒱 _
      (L.isInvertible.pullback g')
  have hdO : IsLocallyConstant (d (𝟙_ (pullback c t).Modules)) :=
    Scheme.TwoAffineOpenCover.isLocallyConstant_finrank_ker_sub_finrank_coker_cechDiff_baseChange πA 𝒱 _
      ((Scheme.Modules.isInvertible_unit _).pullback g')
  have hVopen : IsOpen {𝔭 : PrimeSpectrum A | d L.L 𝔭 = d (𝟙_ (pullback c t).Modules) 𝔭} := by
    have := (hdL.comp₂ hdO (· - ·)).isOpen_fiber 0
    simp only [sub_eq_zero] at this
    exact this

  have key_imp : ∀ (𝔭 : PrimeSpectrum A) (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = j.base 𝔭 →
        (IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L) ↔ d L.L 𝔭 = d (𝟙_ (pullback c t).Modules) 𝔭) := by
    intro 𝔭 k _ _ s hs
    obtain ⟨hint, hprop, hsm⟩ := fibre_inst s
    haveI := hint; haveI := hprop; haveI := hsm
    obtain ⟨𝒲, h𝒲⟩ :=
      exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField c t j πA g' hcart 𝒱 𝔭 s hs
    obtain ⟨hL0, hL1⟩ := h𝒲 L.L L.isInvertible
    obtain ⟨hO0, hO1⟩ := h𝒲 (𝟙_ _) (Scheme.Modules.isInvertible_unit _)
    obtain ⟨hu0, hu1⟩ := chi_unit s 𝒲
    rw [isAlgEquivZero_iff_eulerChar_sectionsOf_eq k (fibreAt c t s) (fibreModule c t s L.L)
      (L.isInvertible.pullback _) 𝒲]
    simp only [d]
    rw [← hu0, ← hu1, hL0, hL1, hO0, hO1]
  refine ⟨j.base '' {𝔭 : PrimeSpectrum A | d L.L 𝔭 = d (𝟙_ (pullback c t).Modules) 𝔭}, ?_,
    j.isOpenEmbedding.isOpenMap _ hVopen, ?_⟩
  ·
    rintro _ ⟨𝔭, h𝔭, rfl⟩ k _ _ s hs
    have hs' : s.base (IsLocalRing.closedPoint k) = j.base 𝔭 := hs ⟨_, rfl⟩
    exact (key_imp 𝔭 k s hs').mpr h𝔭
  ·
    have hxr : x ∈ Set.range ⇑j.base := by
      rw [hjdef]
      change x ∈ Set.range hW.fromSpec
      rw [hW.range_fromSpec]; exact hxW
    obtain ⟨𝔭, rfl⟩ := hxr
    refine ⟨𝔭, ?_, rfl⟩

    let K : Type u := AlgebraicClosure 𝔭.asIdeal.ResidueField
    let sb : Spec (CommRingCat.of K) ⟶ T :=
      Scheme.TwoAffineOpenCover.specMap 𝔭.asIdeal.ResidueField K ≫
        Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField ≫ j
    have hsb : sb.base (IsLocalRing.closedPoint K) = j.base 𝔭 := by
      change j.base ((Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField).base
        ((Scheme.TwoAffineOpenCover.specMap 𝔭.asIdeal.ResidueField K).base (IsLocalRing.closedPoint K))) = j.base 𝔭
      rw [specMap_residueField_base]
    have hrange : Set.range ⇑sb ⊆ {j.base 𝔭} := by
      rintro _ ⟨y, rfl⟩
      rw [Subsingleton.elim y (IsLocalRing.closedPoint K)]
      exact hsb
    exact (key_imp 𝔭 K sb hsb).mp (hx K sb hrange)

end

open Pic0Locus in
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t] (L : RigidifiedLineBundle c ε t) :
    IsOpen {x : T | ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      Set.range ⇑s ⊆ {x} → IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L)}:=
  Pic0Locus.main R c ε h𝔉 t L
