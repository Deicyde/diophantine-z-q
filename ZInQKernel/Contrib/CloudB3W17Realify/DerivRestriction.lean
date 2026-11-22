import ZInQKernel.Contrib.CloudB3W17Realify.Realification
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! # Derivative scalar restriction in unchanged self-model charts -/

open Function Set
open scoped Manifold ContDiff

namespace CloudB3W17Realify

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace F N]

/-- A complex manifold derivative restricts to the real derivative in the same charts. -/
theorem hasMFDerivAt_real {f : M → N} {x : M} {D : E →L[ℂ] F}
    (hf : HasMFDerivAt 𝓘(ℂ, E) 𝓘(ℂ, F) f x D) :
    HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, F) f x (D.restrictScalars ℝ) := by
  rcases hf with ⟨hc, hd⟩
  refine ⟨hc, ?_⟩
  change HasFDerivWithinAt (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, F) x f) D
    (range (𝓘(ℂ, E) : E → E)) (extChartAt 𝓘(ℂ, E) x x) at hd
  change HasFDerivWithinAt (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, F) x f)
    (D.restrictScalars ℝ) (range (𝓘(ℝ, E) : E → E)) (extChartAt 𝓘(ℝ, E) x x)
  simpa only [writtenInExtChartAt,
    extChartAt_eq (I := 𝓘(ℝ, E)) (J := 𝓘(ℂ, E)) rfl,
    extChartAt_eq (I := 𝓘(ℝ, F)) (J := 𝓘(ℂ, F)) rfl,
    modelWithCornersSelf_coe] using hd.restrictScalars ℝ

/-- A real derivative with a complex-linear linear part is a complex manifold derivative. -/
theorem hasMFDerivAt_complex {f : M → N} {x : M} {D : E →L[ℂ] F}
    (hf : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, F) f x (D.restrictScalars ℝ)) :
    HasMFDerivAt 𝓘(ℂ, E) 𝓘(ℂ, F) f x D := by
  rcases hf with ⟨hc, hd⟩
  refine ⟨hc, ?_⟩
  change HasFDerivWithinAt (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, F) x f)
    (D.restrictScalars ℝ) (range (𝓘(ℝ, E) : E → E)) (extChartAt 𝓘(ℝ, E) x x) at hd
  change HasFDerivWithinAt (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, F) x f) D
    (range (𝓘(ℂ, E) : E → E)) (extChartAt 𝓘(ℂ, E) x x)
  have h := hd.of_restrictScalars ℝ (f' := D) rfl
  simpa only [writtenInExtChartAt,
    extChartAt_eq (I := 𝓘(ℝ, E)) (J := 𝓘(ℂ, E)) rfl,
    extChartAt_eq (I := 𝓘(ℝ, F)) (J := 𝓘(ℂ, F)) rfl,
    modelWithCornersSelf_coe] using h

/-- Actual real and complex derivatives agree as maps on the model. -/
theorem mfderiv_real_apply {f : M → N} {x : M}
    (hf : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) f x) (y : E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x y = mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x y := by
  have h := hasMFDerivAt_real (E := E) (F := F) (M := M) (N := N) hf.hasMFDerivAt
  exact congrArg (fun D => D y) h.mfderiv

end CloudB3W17Realify
