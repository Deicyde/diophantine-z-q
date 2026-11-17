import ZInQKernel.Contrib.CloudB3W17bOkaComparison.OriginalPointEquiv
import ZInQKernel.Contrib.CloudB3W17GAGA.CanonicalOriginalPoints
import ZInQKernel.OneProof.H.TailP

/-!
# Actual Oka analytic morphisms of the ORIGINAL abelian-variety complex points

The original CPts carrier, identity embedding, classical topology and canonical
Hodge atlas are retained. The relative dimensions and lifted-base LFT structures
are derived internally from the ORIGINAL AbVar fields. A given native analytic
F/H is lifted to an ACTUAL Oka analytic Hom, with realization at EVERY original
point. No algebraic F/H, target uniformization, GAGA or model premise is added.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic
open scoped Manifold ContDiff Topology CategoryTheory.MonObj
open PkgI3 (AbVar)
open ZInQ.Contrib.CloudB3W17GAGA (APts)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

local instance nativeAbVarIntegral (A : AbVar ℂ) : IsIntegral A.X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom

local instance nativeAbVarTopology (A : AbVar ℂ) : TopologicalSpace (APts A) :=
  CloudB3W17Hodge.classicalTopology A.X

local instance nativeAbVarCharted (A : AbVar ℂ) :
    ChartedSpace (Fin (TopologicalSpace.dim A.X.left) → ℂ) (APts A) :=
  CloudB3W17Hodge.chartedSpace A.X (TopologicalSpace.dim A.X.left)

/-- The ORIGINAL abelian-variety scheme, unchanged, over the actual lifted complex base. -/
def abVarAnalytificationScheme (A : AbVar ℂ) : SchemeLFTℂ :=
  nativeRelativeDimensionLFT A.X (TopologicalSpace.dim A.X.left)

@[simp]
theorem abVarAnalytificationScheme_left (A : AbVar ℂ) :
    (abVarAnalytificationScheme A).obj.left = A.X.left := rfl

@[simp]
theorem abVarAnalytificationScheme_hom (A : AbVar ℂ) :
    (abVarAnalytificationScheme A).obj.hom = A.X.hom ≫ complexULiftBaseIso.hom := rfl

/-- Actual analytic points of the original abelian variety in the ORIGINAL identity-embedding CPts carrier. -/
def abVarAnalytificationPoints (A : AbVar ℂ) :
    analytification.obj (abVarAnalytificationScheme A) ≃ APts A :=
  originalAnalytificationPointEquiv A.X (TopologicalSpace.dim A.X.left)

/-- The ACTUAL Oka analytic Hom of the given ORIGINAL canonically manifold-differentiable point map. -/
def abVarAnalyticOfOriginalMDiff (A B : AbVar ℂ) (F : APts A → APts B)
    (hF : MDifferentiable 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
      𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) F) :
    analytification.obj (abVarAnalytificationScheme A) ⟶ analytification.obj (abVarAnalytificationScheme B) :=
  originalNativeMDifferentiableAnalytic A.X B.X
    (TopologicalSpace.dim A.X.left) (TopologicalSpace.dim B.X.left) F hF

/-- It realizes F at EVERY ORIGINAL CPts point, via the ACTUAL analytification-point equivalence. -/
theorem abVarAnalyticOfOriginalMDiff_apply (A B : AbVar ℂ) (F : APts A → APts B)
    (hF : MDifferentiable 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
      𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) F) (P : APts A) :
    abVarAnalytificationPoints B
      ((abVarAnalyticOfOriginalMDiff A B F hF).toLRSHom.base ((abVarAnalytificationPoints A).symm P)) = F P :=
  originalNativeMDifferentiableAnalytic_originalPoint A.X B.X
    (TopologicalSpace.dim A.X.left) (TopologicalSpace.dim B.X.left) F hF P

/-- The given ORIGINAL Cω point map has an ACTUAL Oka analytic morphism. -/
def abVarAnalyticOfOriginalContMDiff (A B : AbVar ℂ) (F : APts A → APts B)
    (hF : ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
      𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) ω F) :
    analytification.obj (abVarAnalytificationScheme A) ⟶ analytification.obj (abVarAnalytificationScheme B) :=
  abVarAnalyticOfOriginalMDiff A B F (hF.mdifferentiable (by simp))

/-- Its actual analytic map realizes the ORIGINAL Cω function at every original point. -/
theorem abVarAnalyticOfOriginalContMDiff_apply (A B : AbVar ℂ) (F : APts A → APts B)
    (hF : ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
      𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) ω F) (P : APts A) :
    abVarAnalytificationPoints B
      ((abVarAnalyticOfOriginalContMDiff A B F hF).toLRSHom.base ((abVarAnalytificationPoints A).symm P)) = F P :=
  abVarAnalyticOfOriginalMDiff_apply A B F (hF.mdifferentiable (by simp)) P

local instance nativeProductGrp (A B : AbVar ℂ) : GrpObj (AVGlue.prodAbVar A B).X :=
  AbVar.grp (AVGlue.prodAbVar A B)

local instance nativeProductProper (A B : AbVar ℂ) : IsProper (AVGlue.prodAbVar A B).X.hom :=
  AbVar.proper (AVGlue.prodAbVar A B)

local instance nativeProductSmooth (A B : AbVar ℂ) : Smooth (AVGlue.prodAbVar A B).X.hom :=
  AbVar.smooth (AVGlue.prodAbVar A B)

local instance nativeProductGeomIntegral (A B : AbVar ℂ) : GeometricallyIntegral (AVGlue.prodAbVar A B).X.hom :=
  AbVar.geomInt (AVGlue.prodAbVar A B)

local instance nativeProductIntegral (A B : AbVar ℂ) : IsIntegral (AVGlue.prodAbVar A B).X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton (AVGlue.prodAbVar A B).X.hom

local instance nativeProductPointsGroup (A B : AbVar ℂ) : Group (APts (AVGlue.prodAbVar A B)) :=
  inferInstanceAs (Group (ZInQ.LeafPush2.cptObj (RingHom.id ℂ) ⟶ (AVGlue.prodAbVar A B).X))

local instance nativeProductTopology (A B : AbVar ℂ) : TopologicalSpace (APts (AVGlue.prodAbVar A B)) :=
  CloudB3W17Hodge.classicalTopology (AVGlue.prodAbVar A B).X

local instance nativeProductCharted (A B : AbVar ℂ) :
    ChartedSpace (Fin (TopologicalSpace.dim (AVGlue.prodAbVar A B).X.left) → ℂ) (APts (AVGlue.prodAbVar A B)) :=
  CloudB3W17Hodge.chartedSpace (AVGlue.prodAbVar A B).X (TopologicalSpace.dim (AVGlue.prodAbVar A B).X.left)

/-- The bridge applies directly to the ACTUAL scheme-product original-point kernel H.
The input is the actual native group Hom and its proved Cω regularity, never an algebraic H witness. -/
theorem exists_productKernel_analyticMap_original (A B : AbVar ℂ)
    (H : APts (AVGlue.prodAbVar A B) →* APts B)
    (hH : ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim (AVGlue.prodAbVar A B).X.left) → ℂ)
      𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) ω H) :
    ∃ h : analytification.obj (abVarAnalytificationScheme (AVGlue.prodAbVar A B)) ⟶
        analytification.obj (abVarAnalytificationScheme B),
      ∀ P : APts (AVGlue.prodAbVar A B),
        abVarAnalytificationPoints B
          (h.toLRSHom.base ((abVarAnalytificationPoints (AVGlue.prodAbVar A B)).symm P)) = H P :=
  ⟨abVarAnalyticOfOriginalContMDiff (AVGlue.prodAbVar A B) B H hH,
    abVarAnalyticOfOriginalContMDiff_apply (AVGlue.prodAbVar A B) B H hH⟩

end ZInQ.Contrib.CloudB3W17bOkaComparison
