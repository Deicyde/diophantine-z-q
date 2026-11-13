import ZInQKernel.Contrib.Dim.SmoothTrdeg
import ZInQKernel.HDecomp.LeafPush2.R18

/-!
# Dimension and transcendence degree over the kernel's `ffAlgebra`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task dim-contrib, 2026-11-13,
adopting task curve-infra, `scratch/curve-infra/`).

The kernel's `ZInQ.LeafPush2.ffAlgebra X` (`ZInQKernel/HDecomp/LeafPush2/R18.lean`) makes the
function field of an integral `X : Over (Spec K)` a `K`-algebra. It agrees definitionally with
`ZInQ.Contrib.Dim.functionFieldAlgebra K X.left X.hom`, so the Mathlib-only results of
`ZInQKernel.Contrib.Dim.FunctionField` and `ZInQKernel.Contrib.Dim.SmoothTrdeg` apply without
conversion.

## Main results (curve-infra's named statements)

* `dimEqTrdegOver : DimEqTrdegOver`: `dim X = trdeg_K K(X)` for `X` integral, locally of finite
  type over `K`.
* `smoothTrdegOver : SmoothTrdegOver`: `trdeg_K K(X) = n` for `X` integral, smooth of relative
  dimension `n` over `K`.
* `curveAlgOverTranscendental : CurveAlgOverTranscendental`: on a smooth integral curve, `K(X)` is
  algebraic over `K[x]` for every transcendental `x` (compare the kernel's `HasSexticModel`, which
  asks for a transcendental `x`).
-/

namespace ZInQ.Contrib.Dim

open AlgebraicGeometry CategoryTheory

/-- **`DimEqTrdeg` with the kernel's `ZInQ.LeafPush2.ffAlgebra`**, for `X : Over (Spec K)`.
Glue: proved here (`dimEqTrdegOver`). -/
def DimEqTrdegOver : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom],
    letI := ZInQ.LeafPush2.ffAlgebra X
    topologicalKrullDim X.left = ((Algebra.trdeg K X.left.functionField).toENat : WithBot ℕ∞)

/-- **`SmoothTrdeg` with the kernel's `ffAlgebra`.** Glue: proved here (`smoothTrdegOver`). -/
def SmoothTrdegOver : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))) [IsIntegral X.left]
    (n : ℕ) [SmoothOfRelativeDimension n X.hom],
    letI := ZInQ.LeafPush2.ffAlgebra X
    Algebra.trdeg K X.left.functionField = n

/-- **On a smooth integral curve, the function field is algebraic over `K[x]` for every
transcendental `x`** (with the kernel's `ffAlgebra`). Glue: proved here
(`curveAlgOverTranscendental`) from `SmoothTrdegOver` and Mathlib's transcendence bases. -/
def CurveAlgOverTranscendental : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom],
    letI := ZInQ.LeafPush2.ffAlgebra X
    ∀ x : X.left.functionField, Transcendental K x →
      Algebra.IsAlgebraic (Algebra.adjoin K {x}) X.left.functionField

/-- curve-infra's `DimEqTrdegOver`, proved. -/
theorem dimEqTrdegOver : DimEqTrdegOver := by
  intro K _ X _ _
  exact topologicalKrullDim_eq_trdeg_functionField K X.left X.hom

/-- curve-infra's `SmoothTrdegOver`, proved. -/
theorem smoothTrdegOver : SmoothTrdegOver := by
  intro K _ X _ n _
  exact trdeg_functionField_eq_of_smoothOfRelativeDimension K X.left X.hom n

/-- curve-infra's `CurveAlgOverTranscendental`, proved. -/
theorem curveAlgOverTranscendental : CurveAlgOverTranscendental := by
  intro K _ X _ _
  let := ZInQ.LeafPush2.ffAlgebra X
  intro x hxt
  exact isAlgebraic_adjoin_of_transcendental_of_trdeg_eq_one K X.left.functionField
    (by exact_mod_cast smoothTrdegOver K X 1) x hxt

end ZInQ.Contrib.Dim
