/-
Copyright (c) 2026 W17 contributors.
Released under Apache 2.0 license as described in the file LICENSE.

Projective compactness is imported from the immutable Hodge companion port at
9fbc627ae28ffa756cdf33f2c8995eddce06601a. This file uses the surjective projective
Chow cover and the actual native point topology; it does not assume projectivity
or compactness of the target scheme.
-/
import ZInQKernel.Contrib.CloudB3W17ProperCompact.NativePresentation
import ZInQKernel.Contrib.CloudB3W17Hodge.Port.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveCompact

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace W17ProperCompact

/-- The native analytic complex points of an integral proper complex scheme are compact. -/
theorem compactSpace_complexPoint_of_isIntegral_isProper
    (X : Over (Spec (CommRingCat.of ℂ))) [IsProper X.hom] [IsIntegral X.left] :
    @CompactSpace (ComplexPoint X) Point.analyticTopology := by
  obtain ⟨Y, p, hY, hc, hs⟩ := exists_projective_continuous_surjective_point_map X
  let _ : IsProjective Y.hom := hY
  have : CompactSpace (ComplexPoint Y) := inferInstance
  refine ⟨?_⟩
  have h := (isCompact_univ (X := ComplexPoint Y)).image hc
  rwa [Set.image_univ, Set.range_eq_univ.mpr hs] at h

end W17ProperCompact
