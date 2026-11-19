/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Pure SCHEME-geometry consumer of the FROZEN original tensor triple/chart
factorizations. On the exact H-ι locus, the three original generic lifts
have the shared first/middle/last model coordinates. Proofs only cancel
the mono generic-open inclusion, use the original factor/projection
inclusion equations and apply the actual nerve equations 1/2/3.

No Scheme.Modules object, W07/cohomology import, native line comparison,
gamma, psi, line cocycle, extra compatibility or desired effectivity is
introduced. Lane6 retains its entire line/gamma/global-nine-factor proof.
All frozen TensorTriple/GenericTensor/TensorTripleChartGeometry and all
producer files remain unchanged. Compile only in the hash-bound frozen
compatible geometry profile, not the half-updated H5 public W07 epoch.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.TensorTripleChartGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorTripleGenericGeometry
open TensorCofaces TensorNerve TensorTripleChartGeometry

variable {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
  (V : (Base R).Opens) (G : Grp (Over (Cover R'))) (A : Grp (Over V.toScheme))
  (e : (Over.pullback ((baseMap R R') ⁻¹ᵁ V).ι).mapGrp.obj G ≅
    (Over.pullback ((baseMap R R') ∣_ V)).mapGrp.obj A)
  [Etale (baseMap R R')] (c : Base R)
  [Mono ((baseMap R R').fiberToSpecResidueField c)]
  (hV : ∀ z : Base R, z ∉ V → z = c)

/-- The 12 and 13 factors have literally the SAME first generic lift.
    This identity already needs only the original first-chart geometry. -/
theorem shared_generic_first :
    factor12 (R := R) R' V G ≫ genericProjection1 R' V G =
      factor13 (R := R) R' V G ≫ genericProjection1 R' V G := by
  apply (cancel_mono (modelGenericOpen R' V G).ι).mp
  simpa only [Category.assoc, genericProjection1_ι, factor12_ι_assoc, factor13_ι_assoc] using
    congrArg ((H (R := R) R' V G).ι ≫ ·) (nerve_eq1 (R := R) R' G)

/-- The second generic lift of the 12 factor IS the first generic lift of
    the 23 factor, retaining the original chart-2 transport map. -/
theorem shared_generic_middle :
    factor12 (R := R) R' V G ≫ genericProjection2 R' V G A e c hV =
      factor23 R' V G A e c hV ≫ genericProjection1 R' V G := by
  apply (cancel_mono (modelGenericOpen R' V G).ι).mp
  simpa only [Category.assoc, genericProjection1_ι, genericProjection2_ι,
    factor12_ι_assoc, factor23_ι_assoc] using
    congrArg ((H (R := R) R' V G).ι ≫ ·) (nerve_eq2 R' V G A e c hV)

/-- The 23 and 13 factors have literally the SAME last generic lift.
    This uses the proved original SCHEME nerve cocycle, not a line equation. -/
theorem shared_generic_last :
    factor23 R' V G A e c hV ≫ genericProjection2 R' V G A e c hV =
      factor13 (R := R) R' V G ≫ genericProjection2 R' V G A e c hV := by
  apply (cancel_mono (modelGenericOpen R' V G).ι).mp
  simpa only [Category.assoc, genericProjection2_ι, factor23_ι_assoc, factor13_ι_assoc] using
    congrArg ((H (R := R) R' V G).ι ≫ ·) (nerve_eq3 R' V G A e c hV).symm

#print axioms shared_generic_first
#print axioms shared_generic_middle
#print axioms shared_generic_last

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorTripleGenericGeometry
