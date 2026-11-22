/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_isOpen_setOf_forall_fibre_subsingleton_H1. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isPullback_snd_specMap_algebraOfHom
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finiteType_algebraOfHom
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isOpen_setOf_subsingleton_H1_fibre
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_subsingleton_H1_fibre_of_subsingleton_H1_residueField_chart
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isOpen_setOf_forall_fibre_subsingleton_H1

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
-- Original source-local namespace open deferred until after its declaration.
open AlgebraicGeometry.RelPicard
-- Original source-local namespace open deferred until after its declaration.
open NeronModelInfra
open AlgebraicGeometry.SmoothProperCurve

noncomputable section

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (SmoothOfRelativeDimension IsProper Scheme.Modules.pullback LocallyOfFiniteType Spec Scheme IsOpenImmersion Scheme.Modules Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible SmoothProperCurve.FiniteMapData Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom RelPicard.exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom Scheme.TwoAffineOpenCover.finiteType_algebraOfHom Scheme.TwoAffineOpenCover.isOpen_setOf_subsingleton_H1_fibre RelPicard.subsingleton_H1_fibre_of_subsingleton_H1_residueField_chart)
namespace RelPicard
export _root_.AlgebraicGeometry.RelPicard (fibreAt fibreModule exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback subsingleton_H1_fibre_of_subsingleton_H1_residueField_chart)
namespace OpenLocusSol
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry

theorem specMap_residueField_base {A : Type u} [CommRing A] (𝔭 : PrimeSpectrum A) :
    (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField).base
      (IsLocalRing.closedPoint 𝔭.asIdeal.ResidueField) = 𝔭 := by
  apply PrimeSpectrum.ext
  change (PrimeSpectrum.comap (algebraMap A 𝔭.asIdeal.ResidueField)
    (IsLocalRing.closedPoint 𝔭.asIdeal.ResidueField)).asIdeal = 𝔭.asIdeal
  rw [PrimeSpectrum.comap_asIdeal]
  have hbot : (IsLocalRing.closedPoint 𝔭.asIdeal.ResidueField).asIdeal = ⊥ := by
    change IsLocalRing.maximalIdeal _ = ⊥
    exact IsLocalRing.maximalIdeal_eq_bot
  rw [hbot, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

theorem toK4
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)
    {A : Type u} [CommRing A] (j : Spec (CommRingCat.of A) ⟶ T)
    {CA : Scheme.{u}} (g' : CA ⟶ pullback c t) (πA : CA ⟶ Spec (CommRingCat.of A))
    (hcart : IsPullback g' πA (pullback.snd c t) j)
    (𝒱 : CA.TwoAffineOpenCover) (𝔭 : ↥(Spec (CommRingCat.of A)))
    (hU : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = j.base 𝔭 →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1) :
    Subsingleton ((𝒱.pullback πA 𝔭.asIdeal.ResidueField).sectionsOf
        (pullback.snd πA (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (pullback.fst πA (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))).obj
          ((Scheme.Modules.pullback g').obj M))).H1 := by
  let κ := 𝔭.asIdeal.ResidueField
  let s₀ := Scheme.TwoAffineOpenCover.specMap A κ

  have hsq : IsPullback (pullback.fst πA s₀ ≫ g') (pullback.snd πA s₀) (pullback.snd c t) (s₀ ≫ j) :=
    (IsPullback.of_hasPullback πA s₀).paste_horiz hcart
  obtain ⟨𝒲, -, ⟨e1⟩⟩ := RelPicard.exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback c t M (s₀ ≫ j)
    (pullback.snd πA s₀) (pullback.fst πA s₀ ≫ g') hsq
    ((Scheme.Modules.pullback (pullback.fst πA s₀)).obj ((Scheme.Modules.pullback g').obj M))
    ((Scheme.Modules.pullbackComp (pullback.fst πA s₀) g').app M) (𝒱.pullback πA κ)
  have hs : (s₀ ≫ j).base (IsLocalRing.closedPoint κ) = j.base 𝔭 := by
    change j.base (s₀.base (IsLocalRing.closedPoint κ)) = j.base 𝔭
    rw [specMap_residueField_base]
  haveI := hU κ (s₀ ≫ j) hs 𝒲
  exact e1.toEquiv.subsingleton

theorem main
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M) :
    IsOpen {x : T | ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx

  obtain ⟨W, hW, hxW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
    (show x ∈ (⊤ : T.Opens) from trivial)
  letI := Scheme.TwoAffineOpenCover.algebraOfHom t W
  haveI : Algebra.FiniteType R Γ(T, W) := Scheme.TwoAffineOpenCover.finiteType_algebraOfHom t W hW
  haveI : IsNoetherianRing Γ(T, W) := Algebra.FiniteType.isNoetherianRing R _
  obtain ⟨g', hcart, -⟩ := Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom c t W hW
  haveI : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec

  obtain ⟨𝔉, -⟩ := h𝔉 0
  obtain ⟨𝔉A, -, -, -, -⟩ := 𝔉.exists_baseChange Γ(T, W)
  let 𝒱 := 𝔉A.twoAffineOpenCover

  have hO := Scheme.TwoAffineOpenCover.isOpen_setOf_subsingleton_H1_fibre
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W))) 𝒱
    ((Scheme.Modules.pullback g').obj M) (hM.pullback g')
  refine ⟨hW.fromSpec.base '' {𝔭 | Subsingleton
      ((𝒱.pullback (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W))) 𝔭.asIdeal.ResidueField).sectionsOf
        (pullback.snd (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)))
          (Scheme.TwoAffineOpenCover.specMap Γ(T, W) 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)))
          (Scheme.TwoAffineOpenCover.specMap Γ(T, W) 𝔭.asIdeal.ResidueField))).obj
          ((Scheme.Modules.pullback g').obj M))).H1}, ?_, ?_, ?_⟩
  ·
    rintro y ⟨𝔭, h𝔭, rfl⟩
    intro k _ s hs 𝒲
    exact RelPicard.subsingleton_H1_fibre_of_subsingleton_H1_residueField_chart c t M hM hW.fromSpec _ g' hcart 𝒱 𝔭 h𝔭 s hs 𝒲
  ·
    exact hW.fromSpec.isOpenEmbedding.isOpenMap _ hO
  ·
    have hxr : x ∈ Set.range hW.fromSpec.base := by rw [hW.range_fromSpec]; exact hxW
    obtain ⟨𝔭, rfl⟩ := hxr
    exact ⟨𝔭, toK4 c t M hW.fromSpec g' _ hcart 𝒱 𝔭 hx, rfl⟩

end AlgebraicGeometry.RelPicard.OpenLocusSol
open _root_.P2MW.S_AlgebraicGeometry_RelPicard_isOpen_setOf_forall_fibre_subsingleton_H1.AlgebraicGeometry
open _root_.P2MW.S_AlgebraicGeometry_RelPicard_isOpen_setOf_forall_fibre_subsingleton_H1.AlgebraicGeometry.RelPicard

end

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M) :
    IsOpen {x : T | ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1} :=
  AlgebraicGeometry.RelPicard.OpenLocusSol.main R c ε h𝔉 t M hM
