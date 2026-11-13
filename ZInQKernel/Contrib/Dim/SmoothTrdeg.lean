import ZInQKernel.Contrib.Dim.FunctionField
import ZInQKernel.Contrib.Dim.SmoothStalk

/-!
# Function fields of smooth integral schemes over a field

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task dim-contrib, 2026-11-13,
adopting task curve-infra, `scratch/curve-infra/`). Mathlib only.

## Main results

Let `K` be a field and `X` an integral scheme, smooth of relative dimension `n` over `K`.

* `ZInQ.Contrib.Dim.trdeg_functionField_eq_of_smoothOfRelativeDimension`: `trdeg_K K(X) = n`.
* `ZInQ.Contrib.Dim.exists_aeval_eq_zero_of_smoothOfRelativeDimension_one`: if `n = 1`, any two
  rational functions on `X` satisfy a nonzero polynomial relation over `K`.
* `ZInQ.Contrib.Dim.isAlgebraic_adjoin_of_transcendental_of_trdeg_eq_one`: if `trdeg_K F = 1`, then
  `F` is algebraic over `K[x]` for every transcendental `x ∈ F`.

Sources (STANDARD; numbering UNVERIFIED): Hartshorne I Prop. 1.7/Thm. 1.8A with II.8; the Stacks
Project, *Varieties*, section "Smooth varieties". The named statements `SmoothTrdeg` and
`CurveFnFieldAlgDep` are curve-infra's, unchanged up to the name of the algebra structure.
-/

namespace ZInQ.Contrib.Dim

open AlgebraicGeometry CategoryTheory

universe u

/-- **Transcendence degree of the function field of a smooth integral scheme.** If `X` is
integral and smooth of relative dimension `n` over a field `K`, then `trdeg_K K(X) = n`. -/
theorem trdeg_functionField_eq_of_smoothOfRelativeDimension (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n f] :
    letI := functionFieldAlgebra K X f
    Algebra.trdeg K X.functionField = n := by
  let := functionFieldAlgebra K X f
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have h1 := topologicalKrullDim_eq_trdeg_functionField K X f
  have h2 := topologicalKrullDim_eq_of_smoothOfRelativeDimension f n
  rw [h1] at h2
  have h3 : (Algebra.trdeg K X.functionField).toENat = n := by exact_mod_cast h2
  exact Cardinal.toENat_eq_natCast.mp h3

/-- **Two rational functions on a smooth integral curve are algebraically dependent.** -/
theorem exists_aeval_eq_zero_of_smoothOfRelativeDimension_one (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 f] :
    letI := functionFieldAlgebra K X f
    ∀ a b : X.functionField,
      ∃ P : MvPolynomial (Fin 2) K, P ≠ 0 ∧ MvPolynomial.aeval ![a, b] P = 0 := by
  let := functionFieldAlgebra K X f
  have h := trdeg_functionField_eq_of_smoothOfRelativeDimension K X f 1
  exact exists_aeval_eq_zero_of_trdeg_le_one K X.functionField (by rw [h]; simp)

/-- **A field of transcendence degree one is algebraic over `K[x]` for every transcendental
`x`.** -/
theorem isAlgebraic_adjoin_of_transcendental_of_trdeg_eq_one (K F : Type*) [Field K] [Field F]
    [Algebra K F] (h : Algebra.trdeg K F = 1) (x : F) (hxt : Transcendental K x) :
    Algebra.IsAlgebraic (Algebra.adjoin K {x}) F := by
  have hx : AlgebraicIndependent K ![x] := algebraicIndependent_iff_transcendental.mpr hxt
  have hb := hx.isTranscendenceBasis_of_lift_trdeg_le_of_finite (by rw [h]; simp)
  have := hb.isAlgebraic
  rwa [show Set.range ![x] = {x} by simp] at this

/-! ## Named statements (curve-infra) -/

/-- **Transcendence degree of the function field of a smooth integral scheme.** For `X` integral
and smooth of relative dimension `n` over a field `K`, `trdeg_K K(X) = n`. Source as in the module
docstring. Glue: proved here (`smoothTrdeg`) from `DimEqTrdeg` and
`topologicalKrullDim_eq_of_smoothOfRelativeDimension`. -/
def SmoothTrdeg : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K))
    (n : ℕ) [SmoothOfRelativeDimension n f],
    letI := functionFieldAlgebra K X f
    Algebra.trdeg K X.functionField = n

/-- **Two rational functions on a smooth integral curve are algebraically dependent.** The
general form of curve-glue's (AD) at the level of function fields. Glue: proved here
(`curveFnFieldAlgDep`) from `SmoothTrdeg` and `AlgDepOfTrdegOne`. -/
def CurveFnFieldAlgDep : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 f],
    letI := functionFieldAlgebra K X f
    ∀ a b : X.functionField, ∃ P : MvPolynomial (Fin 2) K, P ≠ 0 ∧ MvPolynomial.aeval ![a, b] P = 0

/-- curve-infra's `SmoothTrdeg`, proved. -/
theorem smoothTrdeg : SmoothTrdeg := by
  intro K _ X _ f n _
  exact trdeg_functionField_eq_of_smoothOfRelativeDimension K X f n

/-- curve-infra's `CurveFnFieldAlgDep`, proved. -/
theorem curveFnFieldAlgDep : CurveFnFieldAlgDep := by
  intro K _ X _ f _
  exact exists_aeval_eq_zero_of_smoothOfRelativeDimension_one K X f

end ZInQ.Contrib.Dim
