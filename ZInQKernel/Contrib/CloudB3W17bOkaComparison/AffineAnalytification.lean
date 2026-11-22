import ZInQKernel.Contrib.CloudB3W17bOkaComparison.AffineChartLRS
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Analytification.Scheme

/-!
# The actual native affine inverse chart as an Oka analytic morphism

Oka's genuine analytification universal property is applied to the already
constructed, complex-base-compatible LRS morphism.  The target is the
analytification of the ORIGINAL affine scheme V with only its complex base
spelling changed along Spec(ULift ℂ).  No algebraic F/H or compatibility witness
is supplied as a hypothesis.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace ComplexAnalytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable (z : ComplexPoint X)

/-- The actual native affine neighbourhood is locally of finite type, derived from
its original relative-dimensional smoothness and its actual open immersion. -/
instance actualEtaleNativeScheme_locallyOfFiniteType :
    LocallyOfFiniteType (actualEtaleNativeScheme X d z).hom := by
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  change LocallyOfFiniteType ((actualEtaleDatum X d z).neighborhood.ι ≫ X.hom)
  infer_instance

/-- The unchanged native affine scheme, in Oka's actual LFT scheme category. -/
def actualEtaleSchemeLFT : SchemeLFTℂ :=
  ⟨overULift (actualEtaleNativeScheme X d z),
    overULift_locallyOfFiniteType (actualEtaleNativeScheme X d z)⟩

@[simp]
theorem actualEtaleSchemeLFT_left :
    (actualEtaleSchemeLFT X d z).obj.left = (actualEtaleNativeScheme X d z).left := rfl

/-- The actual analytic morphism α furnished by the genuine affine-chart Γ pullback. -/
def affineChartAnalytic :
    actualEtaleOkaSource X d z ⟶ analytification.obj (actualEtaleSchemeLFT X d z) :=
  (analytificationHomEquiv (actualEtaleOkaSource X d z) (actualEtaleSchemeLFT X d z)).symm
    (affineChartOverLRS X d z)

/-- α's actual analytification comparison is the constructed original-scheme LRS map. -/
theorem affineChartAnalytic_over_fac :
    AnalyticSpace.toOverSpec.map (affineChartAnalytic X d z) ≫
      analytificationπ (actualEtaleSchemeLFT X d z) = affineChartOverLRS X d z :=
  (analytificationHomEquiv_apply (affineChartAnalytic X d z)).symm.trans
    ((analytificationHomEquiv (actualEtaleOkaSource X d z) (actualEtaleSchemeLFT X d z)).apply_symm_apply
      (affineChartOverLRS X d z))

/-- The commuting square at the actual locally ringed-space level. -/
theorem affineChartAnalytic_lrs_fac :
    (affineChartAnalytic X d z).toLRSHom ≫
      (analytificationπ (actualEtaleSchemeLFT X d z)).left = affineChartToNativeLRS X d z :=
  congrArg (fun f => f.left) (affineChartAnalytic_over_fac X d z)

end ZInQ.Contrib.CloudB3W17bOkaComparison
