/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
-- Deferred synthetic P2M scope; existing root namespace retained.
open AlgebraicGeometry.RelPicard
-- Deferred synthetic P2M scope; existing root namespace retained.
open NeronModelInfra
open AlgebraicGeometry.SmoothProperCurve

noncomputable section

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.Modules.pullback Spec Scheme Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.pullbackComp Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso)
namespace RelPicard
export _root_.AlgebraicGeometry.RelPicard (fibreAt fibreModule)
namespace TransportGen
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry

variable {R : Type u} [CommRing R] {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)
  {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
  {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k)) (g' : Y ⟶ pullback c t)
  (hcart : IsPullback g' y (pullback.snd c t) s)

def φ : pullback (pullback.snd c t) s ≅ Y := hcart.isoPullback.symm

theorem φ_hom_y : (φ c t s y g' hcart).hom ≫ y = fibreAt c t s := by
  rw [φ, Iso.symm_hom, IsPullback.isoPullback_inv_snd]
  rfl

def modIso : fibreModule c t s M ≅ (Scheme.Modules.pullback (φ c t s y g' hcart).hom).obj ((Scheme.Modules.pullback g').obj M) :=
  (Scheme.Modules.pullbackCongr (hcart.isoPullback_inv_fst).symm).app M ≪≫
    (Scheme.Modules.pullbackComp (φ c t s y g' hcart).hom g').symm.app M

include hcart in
theorem main (F : Y.Modules) (e : F ≅ (Scheme.Modules.pullback g').obj M) (𝒱 : Y.TwoAffineOpenCover) :
    ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf y F).H0 ≃ₗ[k] (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0) ∧
      Nonempty ((𝒱.sectionsOf y F).H1 ≃ₗ[k] (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1) := by
  obtain ⟨𝒲, -, -, ⟨eH0⟩, ⟨eH1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t s) y (φ c t s y g' hcart) (φ_hom_y c t s y g' hcart)
    𝒱 F (fibreModule c t s M)
    (modIso c t M s y g' hcart ≪≫ (Scheme.Modules.pullback (φ c t s y g' hcart).hom).mapIso e.symm)
  exact ⟨𝒲, ⟨eH0.symm⟩, ⟨eH1.symm⟩⟩

end AlgebraicGeometry.RelPicard.TransportGen

end

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k)) (g' : Y ⟶ pullback c t)
    (hcart : IsPullback g' y (pullback.snd c t) s)
    (F : Y.Modules) (e : F ≅ (Scheme.Modules.pullback g').obj M) (𝒱 : Y.TwoAffineOpenCover) :
    ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf y F).H0 ≃ₗ[k] (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0) ∧
      Nonempty ((𝒱.sectionsOf y F).H1 ≃ₗ[k] (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1) :=
  AlgebraicGeometry.RelPicard.TransportGen.main c t M s y g' hcart F e 𝒱
