import ZInQKernel.Contrib.CloudB3W17bGAGA.CanonicalAnalyticGraph
import ZInQKernel.Contrib.CloudB3W17Uniformization.CanonicalAnalytic
import ZInQKernel.Contrib.CloudB3W17Uniformization.AbelianPointLieGroup
import ZInQKernel.OneProof.H.TailP

open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 (AbVar)
open ZInQ.LeafPush2 (CPts cptObj)
open ZInQ.Contrib.CloudB3W17GAGA

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bKernel

attribute [local instance] ZInQ.Contrib.CloudB3W17bGAGA.cptsIntegral
  ZInQ.Contrib.CloudB3W17bGAGA.cptsTopology
  ZInQ.Contrib.CloudB3W17bGAGA.cptsChartedSpace
  ZInQ.Contrib.CloudB3W17bGAGA.cptsManifold

local instance cptTopology (X : Over (Spec (CommRingCat.of ℂ))) :
    TopologicalSpace (CloudB3W17Hodge.CPt X) := CloudB3W17Hodge.classicalTopology X

local instance cptCharted (X : Over (Spec (CommRingCat.of ℂ))) (n : ℕ)
    [SmoothOfRelativeDimension n X.hom] :
    ChartedSpace (Fin n → ℂ) (CloudB3W17Hodge.CPt X) := CloudB3W17Hodge.chartedSpace X n

local instance cptManifold (X : Over (Spec (CommRingCat.of ℂ))) (n : ℕ)
    [SmoothOfRelativeDimension n X.hom] :
    IsManifold 𝓘(ℂ, Fin n → ℂ) ω (CloudB3W17Hodge.CPt X) :=
  CloudB3W17Hodge.isManifold_cpt X n

/-- Explicit existing product fields, keeping elaboration on the genuine product object. -/
local instance prodGeomInt (A B : AbVar ℂ) : GeometricallyIntegral (AVGlue.prodAbVar A B).X.hom :=
  AbVar.geomInt (AVGlue.prodAbVar A B)

local instance prodSmooth (A B : AbVar ℂ) : Smooth (AVGlue.prodAbVar A B).X.hom :=
  AbVar.smooth (AVGlue.prodAbVar A B)

local instance prodIntegral (A B : AbVar ℂ) : IsIntegral (AVGlue.prodAbVar A B).X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton (AVGlue.prodAbVar A B).X.hom

local instance prodTopology (A B : AbVar ℂ) : TopologicalSpace (APts (AVGlue.prodAbVar A B)) :=
  CloudB3W17Hodge.classicalTopology (AVGlue.prodAbVar A B).X

local instance prodCharted (A B : AbVar ℂ) (n : ℕ)
    [SmoothOfRelativeDimension n (AVGlue.prodAbVar A B).X.hom] :
    ChartedSpace (Fin n → ℂ) (APts (AVGlue.prodAbVar A B)) :=
  CloudB3W17Hodge.chartedSpace (AVGlue.prodAbVar A B).X n

local instance prodManifold (A B : AbVar ℂ) (n : ℕ)
    [SmoothOfRelativeDimension n (AVGlue.prodAbVar A B).X.hom] :
    IsManifold 𝓘(ℂ, Fin n → ℂ) ω (APts (AVGlue.prodAbVar A B)) :=
  CloudB3W17Hodge.isManifold_cpt (AVGlue.prodAbVar A B).X n

/-- The actual first projection acts on the original complex point groups. -/
def fstPointHom (A B : AbVar ℂ) : APts (AVGlue.prodAbVar A B) →* APts A :=
  IsMonHom.monoidHom (fst A.X B.X) (cptObj (RingHom.id ℂ))

/-- The actual second projection acts on the original complex point groups. -/
def sndPointHom (A B : AbVar ℂ) : APts (AVGlue.prodAbVar A B) →* APts B :=
  IsMonHom.monoidHom (snd A.X B.X) (cptObj (RingHom.id ℂ))

/-- The native point homomorphism whose kernel is the graph of F. Algebraicity is not asserted. -/
def differenceHom (A B : AbVar ℂ) (F : APts A →* APts B) :
    APts (AVGlue.prodAbVar A B) →* APts B :=
  sndPointHom A B * (F.comp (fstPointHom A B))⁻¹

@[simp]
theorem differenceHom_apply (A B : AbVar ℂ) (F : APts A →* APts B)
    (P : APts (AVGlue.prodAbVar A B)) :
    differenceHom A B F P = (P ≫ snd A.X B.X) * (F (P ≫ fst A.X B.X))⁻¹ := rfl

/-- The kernel condition is precisely the original-point graph condition. -/
theorem differenceHom_eq_one_iff (A B : AbVar ℂ) (F : APts A →* APts B)
    (P : APts (AVGlue.prodAbVar A B)) :
    differenceHom A B F P = 1 ↔ F (P ≫ fst A.X B.X) = P ≫ snd A.X B.X := by
  rw [differenceHom_apply, mul_inv_eq_one]
  exact eq_comm

/-- Exact original-point graph image, expressed as the kernel condition on actual product points. -/
theorem graph_iff_exists_kernelPoint (A B : AbVar ℂ) (F : APts A →* APts B)
    (P : APts A) (Q : APts B) :
    F P = Q ↔ ∃ R : APts (AVGlue.prodAbVar A B),
      differenceHom A B F R = 1 ∧ R ≫ fst A.X B.X = P ∧ R ≫ snd A.X B.X = Q := by
  constructor
  · intro h
    refine ⟨lift P Q, ?_, lift_fst P Q, lift_snd P Q⟩
    rw [differenceHom_eq_one_iff, lift_fst, lift_snd]
    exact h
  · rintro ⟨R, hR, hP, hQ⟩
    have h := (differenceHom_eq_one_iff A B F R).mp hR
    rwa [hP, hQ] at h

/-- The actual point-group law is analytic in the unchanged canonical atlas. -/
theorem lieGroup_canonical (B : AbVar ℂ) :
    LieGroup 𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) ω (APts B) := by
  have : IsIntegral (B.X ⊗ B.X).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton (AVGlue.prodAbVar B B).X.hom
  have : Smooth (B.X ⊗ B.X).hom := AbVar.smooth (AVGlue.prodAbVar B B)
  exact CloudB3W17Uniformization.lieGroup_of_analyticRegularMaps B
    (TopologicalSpace.dim B.X.left) (TopologicalSpace.dim (B.X ⊗ B.X).left)
    (fun α => CloudB3W17Uniformization.contMDiff_canonicalMap B.X B.X _ _ α)
    (fun α => CloudB3W17Uniformization.contMDiff_canonicalMap (B.X ⊗ B.X) B.X _ _ α)
    (fun α => CloudB3W17Uniformization.contMDiff_canonicalMap B.X (B.X ⊗ B.X) _ _ α)

/-- A canonical analytic F gives a canonical analytic group homomorphism H on the actual A×B. -/
theorem contMDiff_differenceHom (A B : AbVar ℂ) (F : APts A →* APts B)
    (hF : ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
      𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) ω F) :
    ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim (AVGlue.prodAbVar A B).X.left) → ℂ)
      𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) ω (differenceHom A B F) := by
  have : IsIntegral (A.X ⊗ B.X).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton (AVGlue.prodAbVar A B).X.hom
  have : Smooth (A.X ⊗ B.X).hom := AbVar.smooth (AVGlue.prodAbVar A B)
  let : LieGroup 𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) ω (APts B) := lieGroup_canonical B
  have h₁ : ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim (A.X ⊗ B.X).left) → ℂ)
      𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ) ω (fstPointHom A B) :=
    CloudB3W17Uniformization.contMDiff_canonicalMap (A.X ⊗ B.X) A.X _ _ (fst A.X B.X)
  have h₂ : ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim (A.X ⊗ B.X).left) → ℂ)
      𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) ω (sndPointHom A B) :=
    CloudB3W17Uniformization.contMDiff_canonicalMap (A.X ⊗ B.X) B.X _ _ (snd A.X B.X)
  exact h₂.mul (hF.comp h₁).inv

/-- The original hφ,hψ,hΛ supply H without a target presentation or algebraic-map witness. -/
theorem exists_analytic_kernelHom_original (A B : AbVar ℂ) {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ]
    (φ : BPAnalytic.Torus Λ ≃+ Additive (APts A))
    (hφ : ZInQ.HomLattice.IsStrongUnif A (RingHom.id ℂ) Λ φ)
    {ψ : (Fin g → ℂ) → APts B}
    (hψ : ZInQ.HomLattice.IsAnalyticHom (RingHom.id ℂ) ψ) (hΛ : ∀ z ∈ Λ, ψ z = 1) :
    ∃ H : APts (AVGlue.prodAbVar A B) →* APts B,
      ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim (AVGlue.prodAbVar A B).X.left) → ℂ)
        𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) ω H ∧
      ∀ P, H P = 1 ↔ pointDescentHom φ hψ hΛ (P ≫ fst A.X B.X) = P ≫ snd A.X B.X := by
  let F := pointDescentHom φ hψ hΛ
  have hF := ZInQ.Contrib.CloudB3W17bGAGA.contMDiff_pointDescentHom_canonical A B φ hφ hψ hΛ
  exact ⟨differenceHom A B F, contMDiff_differenceHom A B F hF,
    differenceHom_eq_one_iff A B F⟩

end ZInQ.Contrib.CloudB3W17bKernel

