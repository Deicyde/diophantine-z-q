import ZInQKernel.Contrib.CloudB3W17Realify.ScalarRestriction
import Mathlib.Analysis.Complex.Basic

/-!
# Realification of complex analytic manifolds and Lie groups

Convenient specializations of scalar restriction to `ℂ → ℝ`. The real scalar
 action must be the restriction of the complex action, as recorded by
`IsScalarTower ℝ ℂ E`. Topologies, charted spaces, and group operations are
unchanged. In particular all statements apply with `n = ω`, not only `n = ∞`.

These are partial foundations for the complex Lie-group uniformization route.
They do not construct an exponential map or discharge H103/H105.
-/

open scoped Manifold ContDiff

namespace CloudB3W17Realify

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace F N] {n : ℕ∞ω}

/-- A complex `C^n` self-model manifold is a real `C^n` manifold with the same charts. -/
theorem isManifold_real [IsManifold 𝓘(ℂ, E) n M] : IsManifold 𝓘(ℝ, E) n M :=
  isManifold_self (𝕜 := ℝ) (𝕜' := ℂ)

/-- A complex `C^n` map between self-model manifolds is real `C^n`. -/
theorem contMDiff_real {f : M → N} (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) n f) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) n f :=
  contMDiff_self (𝕜 := ℝ) (𝕜' := ℂ) hf

/-- A complex `C^n` Lie group is a real `C^n` Lie group without changing its charts. -/
theorem lieGroup_real {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup 𝓘(ℂ, E) n G] : LieGroup 𝓘(ℝ, E) n G :=
  lieGroup_self (𝕜 := ℝ) (𝕜' := ℂ)

/-- A complex additive `C^n` Lie group is a real additive `C^n` Lie group. -/
theorem lieAddGroup_real {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [AddGroup G]
    [LieAddGroup 𝓘(ℂ, E) n G] : LieAddGroup 𝓘(ℝ, E) n G :=
  lieAddGroup_self (𝕜 := ℝ) (𝕜' := ℂ)

end CloudB3W17Realify
