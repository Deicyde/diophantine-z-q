import ZInQKernel.Contrib.CloudB3W17bIdentity.Analytic
import ZInQKernel.Contrib.CloudB3W17bAnalyticIdeal.PulledIdeal

/-!
# The pulled identity ideal of the original abelian variety

The generic pulled-ideal construction of `ZInQ.Contrib.CloudB3W17bAnalyticIdeal` is applied,
without redefinition, to the actual identity section `identitySection B`. For an arbitrary
morphism of locally ringed spaces `H : X ⟶ (abVarAnalytificationScheme B)^an` out of a complex
analytic space (nothing algebraic is assumed of `H`; in particular the global analytic maps
`abVarAnalyticOfOriginalMDiff` qualify through `toLRSHom`), the resulting coherent ideal vanishes
exactly where `π_B ∘ H` hits the original identity point.
-/

open CategoryTheory AlgebraicGeometry ComplexAnalytic
open ZInQ.Contrib.CloudB3W17bOkaComparison ZInQ.Contrib.CloudB3W17bAnalyticIdeal

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bIdentity

variable (B : PkgI3.AbVar ℂ) {X : AnalyticSpace.{0}}
  (H : X.toLocallyRingedSpace ⟶
    (analytification.obj (abVarAnalytificationScheme B)).toLocallyRingedSpace)

/-- The identity ideal of the original `B`, pulled back along `H`, is coherent. -/
theorem isCoherent_pulledIdentityIdeal : (pulledIdeal (identitySection B) H).IsCoherent :=
  isCoherent_pulledIdeal (identitySection B) H

/-- **Its vanishing locus is where `π_B ∘ H` equals the original identity point.** -/
theorem vanishingLocus_pulledIdentityIdeal :
    vanishingLocus (invImageIdealι H
        (closedIdealι (analytification.map (identitySection B)).toLRSHom)) =
      H.base ⁻¹' ((analytificationπLRS (abVarAnalytificationScheme B)).base ⁻¹'
        {identityPoint B}) := by
  rw [vanishingLocus_pulledIdeal, range_analytification_identitySection]

end ZInQ.Contrib.CloudB3W17bIdentity
