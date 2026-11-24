import ZInQKernel.Contrib.CloudB3W17bOkaComparison.AffineComparisonPoints
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.IntrinsicContinuity

/-!
# One-direction actual native point topology from the genuine analytic comparison

Every regular-ring evaluation is an actual continuous residue function by the
proved intrinsic analytic local-model argument. Pointwise Γ-algebra topology
and the unchanged native affine point homeomorphism therefore give native
continuity. No native/Oka topology compatibility witness is assumed.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable (Y : Over (Spec (CommRingCat.of ℂ))) (e : ℕ) [SmoothOfRelativeDimension e Y.hom]
variable (q : ComplexPoint Y) (Z : AnalyticSpace.{0})

local instance comparisonTopologyComplexAlgebra : Algebra ℂ Γ((actualEtaleNativeScheme Y e q).left, ⊤) :=
  (actualEtaleDatum Y e q).coordinateRingComplexAlgebra

/-- The true analytic comparison gives a continuous map into the UNCHANGED native affine topology. -/
theorem continuous_affineComparisonPoint
    (f : Z.toLocallyRingedSpace ⟶ (actualEtaleNativeScheme Y e q).left.toLocallyRingedSpace)
    (hbase : f ≫ (overULift (actualEtaleNativeScheme Y e q)).hom.toLRSHom = Z.toSpecℂ) :
    Continuous (affineComparisonPoint Y e q Z f hbase) := by
  have ha : Continuous (affineComparisonAlgHom Y e q Z f hbase) := by
    rw [continuous_induced_rng]
    exact continuous_pi fun r => intrinsic_continuous_eval_top Z ((LocallyRingedSpace.Γ.map f.op).hom r)
  exact (actualEtaleDatum Y e q).pointAlgHomHomeomorph.symm.continuous.comp ha

/-- Actual native open neighbourhoods pull back to actual analytic opens, proving the
one-direction neighbourhood transfer needed to select the native branch of an étale chart. -/
theorem isOpen_affineComparisonPoint_preimage
    (f : Z.toLocallyRingedSpace ⟶ (actualEtaleNativeScheme Y e q).left.toLocallyRingedSpace)
    (hbase : f ≫ (overULift (actualEtaleNativeScheme Y e q)).hom.toLRSHom = Z.toSpecℂ)
    (N : Set (ComplexPoint (actualEtaleNativeScheme Y e q))) (hN : IsOpen N) :
    IsOpen ((affineComparisonPoint Y e q Z f hbase) ⁻¹' N) :=
  hN.preimage (continuous_affineComparisonPoint Y e q Z f hbase)

end ZInQ.Contrib.CloudB3W17bOkaComparison
