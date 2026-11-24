/-
Copyright (c) 2026 W17 contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ZInQKernel.Contrib.CloudB3W17ProperCompact.NativeCompact
import ZInQKernel.HDecomp.Objects

noncomputable section

open AlgebraicGeometry

namespace W17ProperCompact

/-- Native analytic compactness for every actual complex abelian variety. -/
theorem compactSpace_complexPoint_abVar (A : PkgI3.AbVar ℂ) :
    @CompactSpace (ComplexPoint A.X) Point.analyticTopology := by
  have : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  exact compactSpace_complexPoint_of_isIntegral_isProper A.X

end W17ProperCompact
