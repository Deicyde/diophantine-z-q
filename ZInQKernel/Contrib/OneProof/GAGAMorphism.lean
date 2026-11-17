import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Analytification.GAGA.ProjectiveGAGA3
import ZInQKernel.Contrib.CloudB3W17bIdentity.ProjectiveCompat
import ZInQKernel.Contrib.CloudB3W17bCanonicalImage.OriginalKernelLocus
import ZInQKernel.Contrib.CloudB3W17bCanonicalImage.IsoSupport
import ZInQKernel.Contrib.CloudB3W17bGraphScoutReverseIdeal.OriginalKernelGraph

/-!
# GAGAMorphism from projective coherent GAGA

The contract is exactly `ZInQ.HomLattice.GAGAMorphism` (TailQ.lean:875–881).
This file imports no SupportOnly module and takes no GAGA, point-model, kernel,
or graph premise. It constructs the coherent identity ideal through the actual
original-point H, algebraizes its module and inclusion by genuine GAGA-3/GAGA-Hom,
and extracts the native reduced closed group and original-point projection.
The original source/target schemes, point carriers and hypotheses are unchanged.
-/

open CategoryTheory AlgebraicGeometry ComplexAnalytic TopologicalSpace MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Manifold ContDiff Topology CategoryTheory.MonObj
open PkgI3 (AbVar)
open ZInQ.Contrib.CloudB3W17GAGA
open ZInQ.Contrib.CloudB3W17bKernel
open ZInQ.Contrib.CloudB3W17bOkaComparison
open ZInQ.Contrib.CloudB3W17bIdentity
open ZInQ.Contrib.CloudB3W17bAnalyticIdeal
open ZInQ.Contrib.CloudB3W17bCanonicalImage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section
namespace ZInQ.Contrib.OneProof.GAGAMorphism

local instance productionIntegral (A : AbVar ℂ) : IsIntegral A.X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
local instance productionTopology (A : AbVar ℂ) : TopologicalSpace (APts A) :=
  CloudB3W17Hodge.classicalTopology A.X
local instance productionCharted (A : AbVar ℂ) :
    ChartedSpace (Fin (TopologicalSpace.dim A.X.left) → ℂ) (APts A) :=
  CloudB3W17Hodge.chartedSpace A.X (TopologicalSpace.dim A.X.left)
local instance productionProductGeomInt (A B : AbVar ℂ) :
    GeometricallyIntegral (AVGlue.prodAbVar A B).X.hom := AbVar.geomInt (AVGlue.prodAbVar A B)
local instance productionProductIntegral (A B : AbVar ℂ) :
    IsIntegral (AVGlue.prodAbVar A B).X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton (AVGlue.prodAbVar A B).X.hom
local instance productionProductSmooth (A B : AbVar ℂ) :
    Smooth (AVGlue.prodAbVar A B).X.hom := AbVar.smooth (AVGlue.prodAbVar A B)
local instance productionProductTopology (A B : AbVar ℂ) :
    TopologicalSpace (APts (AVGlue.prodAbVar A B)) :=
  CloudB3W17Hodge.classicalTopology (AVGlue.prodAbVar A B).X
local instance productionProductCharted (A B : AbVar ℂ) :
    ChartedSpace (Fin (TopologicalSpace.dim (AVGlue.prodAbVar A B).X.left) → ℂ)
      (APts (AVGlue.prodAbVar A B)) :=
  CloudB3W17Hodge.chartedSpace (AVGlue.prodAbVar A B).X
    (TopologicalSpace.dim (AVGlue.prodAbVar A B).X.left)

/-- Every original analytic homomorphism killing the source lattice is realized
by a morphism of the unchanged original complex abelian varieties. -/
theorem gagaMorphism_proof : ZInQ.HomLattice.GAGAMorphism := by
  intro A B g Λ _ φ hφ ψ hψ hΛ
  let F := pointDescentHom φ hψ hΛ
  have hF := ZInQ.Contrib.CloudB3W17bGAGA.contMDiff_pointDescentHom_canonical A B φ hφ hψ hΛ
  let X := abVarAnalytificationScheme (AVGlue.prodAbVar A B)
  have hX : IsProjectiveℂ X := abVarAnalytificationScheme_isProjective (AVGlue.prodAbVar A B)
  let H := differenceHom A B F
  let hH := contMDiff_differenceHom A B F hF
  let h := abVarAnalyticOfOriginalContMDiff (AVGlue.prodAbVar A B) B H hH
  let I := pulledIdeal (identitySection B) h.toLRSHom
  let j := invImageIdealι h.toLRSHom (closedIdealι (analytification.map (identitySection B)).toLRSHom)
  have hI : I.IsCoherent := isCoherent_actual_originalKernelIdeal A B H hH

  -- Genuine GAGA-3: actual coherent algebraic module and actual source isomorphism.
  obtain ⟨M, hM, ⟨e⟩⟩ := ComplexAnalytic.gaga₃ X hX I hI
  letI := hM
  haveI : LocallyOfFiniteType X.obj.hom := X.property
  haveI : IsLocallyNoetherian X.obj.left := LocallyOfFiniteType.isLocallyNoetherian X.obj.hom
  haveI : (SheafOfModules.unit X.obj.left.ringSheaf).IsCoherent := X.obj.left.isCoherentStructureSheaf
  let a := e.hom ≫ j ≫ (analytificationModulesUnitIso X).inv
  -- Genuine GAGA-Hom: actual algebraic inclusion and its exact unit comparison equation.
  obtain ⟨i, hi⟩ :=
    (ComplexAnalytic.gaga₂ X hX M (SheafOfModules.unit X.obj.left.ringSheaf)).2 a
  have he : (analytificationModules X).map i ≫ (analytificationModulesUnitIso X).hom = e.hom ≫ j := by
    rw [hi]
    simp only [a, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hm : invImageMap (analytificationπLRS X) i = e.hom ≫ j := he
  let J := nativeIdealOfCanonicalCoherentHom (A.X ⊗ B.X).left M i
  have hs : (analytificationπLRS X).base ⁻¹' (J.support : Set (A.X ⊗ B.X).left) =
      {x | H (abVarAnalytificationPoints (AVGlue.prodAbVar A B) x) = 1} := by
    calc
      _ = vanishingLocus (invImageMap (analytificationπLRS X) i) :=
        nativeIdeal_pullback_support_eq X.obj.left M i _ (analytificationπLRS X)
      _ = vanishingLocus (e.hom ≫ j) := congrArg vanishingLocus hm
      _ = vanishingLocus j := vanishingLocus_iso_source e j
      _ = _ := vanishingLocus_actual_originalKernelIdeal A B H hH
  have hJ : ∀ R : APts (AVGlue.prodAbVar A B),
      differenceHom A B F R = 1 ↔ R.left (IsLocalRing.closedPoint ℂ) ∈ J.support := by
    intro R
    let x := (abVarAnalytificationPoints (AVGlue.prodAbVar A B)).symm R
    have hp : (analytificationπLRS X).base x = R.left (IsLocalRing.closedPoint ℂ) := by
      have hc := originalAnalytificationPoint_underlying
        (AVGlue.prodAbVar A B).X (TopologicalSpace.dim (AVGlue.prodAbVar A B).X.left) x
      change (abVarAnalytificationPoints (AVGlue.prodAbVar A B) x).left
          (IsLocalRing.closedPoint ℂ) = (analytificationπLRS X).base x at hc
      rw [show abVarAnalytificationPoints (AVGlue.prodAbVar A B) x = R from
        (abVarAnalytificationPoints (AVGlue.prodAbVar A B)).apply_symm_apply R] at hc
      exact hc.symm
    have hx := (congrArg (fun S : Set (analytification.obj X) => x ∈ S) hs).to_iff
    change (analytificationπLRS X).base x ∈ J.support ↔
      H (abVarAnalytificationPoints (AVGlue.prodAbVar A B) x) = 1 at hx
    rw [hp] at hx
    simpa only [x, Equiv.apply_symm_apply, H] using hx.symm
  obtain ⟨f, hf⟩ :=
    ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal.exists_scheme_realization_of_original_kernel_support
      A B F J.support hJ
  exact ⟨f, fun z => (pointDescentHom_spec φ hψ hΛ z).symm.trans (hf _)⟩

end ZInQ.Contrib.OneProof.GAGAMorphism
