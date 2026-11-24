import ZInQKernel.Contrib.CloudB3W17bOkaComparison.AffineAnalytification
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.AffineGammaLRS

/-!
# Genuine affine analytification constructors for the unchanged native schemes

The actual LRS/Γ constructors are independently factored in AffineGammaLRS.
Here the real, constant-compatible maps are lifted by the actual analytification
universal property. No algebraic F/H or compatibility witness is assumed.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

/-- An unchanged native LFT complex scheme, as Oka's actual LFT object. -/
def nativeSchemeLFT (X : Over (Spec (CommRingCat.of ℂ))) [LocallyOfFiniteType X.hom] : SchemeLFTℂ :=
  ⟨overULift X, (inferInstance : LocallyOfFiniteType (overULift X).hom)⟩

/-- A genuine native scheme morphism with only the complex-base spelling changed. -/
def nativeSchemeLFTMap {X Y : Over (Spec (CommRingCat.of ℂ))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) :
    nativeSchemeLFT X ⟶ nativeSchemeLFT Y := ObjectProperty.homMk (overULiftMap f)

variable (Y : Over (Spec (CommRingCat.of ℂ))) (e : ℕ) [SmoothOfRelativeDimension e Y.hom]
variable (q : ComplexPoint Y) (Z : AnalyticSpace)
variable (μ : Γ((actualEtaleNativeScheme Y e q).left, ⊤) →+* Z.presheaf.obj (op ⊤))
variable (hμ : ∀ c, μ (actualEtaleNativeConst Y e q c) = Z.algebraMap c)

/-- The genuine analytic morphism induced by the actual affine regular-ring pullback. -/
def actualAffineGammaAnalytic : Z ⟶ analytification.obj (actualEtaleSchemeLFT Y e q) :=
  (analytificationHomEquiv Z (actualEtaleSchemeLFT Y e q)).symm (actualAffineGammaOver Y e q Z μ hμ)

/-- Its actual analytification comparison is the constructed affine LRS map. -/
theorem actualAffineGammaAnalytic_fac :
    (actualAffineGammaAnalytic Y e q Z μ hμ).toLRSHom ≫
      (analytificationπ (actualEtaleSchemeLFT Y e q)).left = actualAffineGammaLRS Y e q Z μ := by
  have H := (analytificationHomEquiv_apply (actualAffineGammaAnalytic Y e q Z μ hμ)).symm.trans
    ((analytificationHomEquiv Z (actualEtaleSchemeLFT Y e q)).apply_symm_apply
      (actualAffineGammaOver Y e q Z μ hμ))
  exact congrArg (fun f => f.left) H

/-- The analytic construction still pulls back ALL actual target regular sections by μ. -/
theorem actualAffineGammaAnalytic_gamma_pullback :
    (LocallyRingedSpace.Γ.map
      ((actualAffineGammaAnalytic Y e q Z μ hμ).toLRSHom ≫
        (analytificationπ (actualEtaleSchemeLFT Y e q)).left).op).hom = μ := by
  rw [actualAffineGammaAnalytic_fac]
  exact actualAffineGammaLRS_gamma_pullback Y e q Z μ

end ZInQ.Contrib.CloudB3W17bOkaComparison
