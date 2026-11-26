import ZInQKernel.Contrib.OneProof.AlgebraicHolomorphicCovector
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ChartComparison
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.SourceLimit
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ModelSource

/-! Core objects for comparing weight-two cusp forms on `Γ₀(N)` with global relative
differentials of the complexified modular curve: the curve, the analytic point map
`τ ↦ P τ` given by the actual analytic arc, and the native value `f_ω(τ)` of a global
differential, namely the holomorphic covector of `ω` at `P τ` applied to the derivative
of `P` at `τ`. -/

noncomputable section

open AlgebraicGeometry CategoryTheory UpperHalfPlane
open scoped Manifold

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

open J0Cusps

variable (N : ℕ) [NeZero N]

/-- The complexified modular curve: the Cartesian base change of the model along
`Spec ℂ → Spec ℚ`. -/
abbrev curveC : Over (Spec (.of ℂ)) := complexBaseChange.obj (source N)

instance curveC_smooth : SmoothOfRelativeDimension 1 (curveC N).hom := by
  letI := model_smooth_one N
  change SmoothOfRelativeDimension 1
    (Limits.pullback.snd (source N).hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))))
  infer_instance

/-- The analytic point map `τ ↦ P τ`. -/
def arcPoint (τ : ℍ) : ComplexPoint (curveC N) :=
  complexLift (interior N τ)

/-- The native value of a global relative differential at `τ`. -/
def nativeValue (ω : Γ((curveC N).hom.relativeDifferentials, ⊤)) (τ : ℍ) : ℂ :=
  ComplexPoint.covectorOfSection ω (arcPoint N τ)
    (mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) (arcPoint N) τ (1 : ℂ))

end ZInQ.Manuscript.RC.CuspFormDifferentials
