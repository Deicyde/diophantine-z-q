import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.Inverse
import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.FunctionFieldProof

/-! Route B, lane W-F, assembled with the proved P1: `Ψ` and the linear equivalence between
global differentials of `curveC N` and weight-two cusp forms on `Γ₀(N)`, from K8–K12 only. -/

noncomputable section

open AlgebraicGeometry UpperHalfPlane

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

variable (N : ℕ) [NeZero N]

/-- The hypotheses for `Ψ`, with P1 discharged by its proof. -/
theorem psiHypotheses (h10 : K10 N) (h11a : K11Arc N) (h11c : K11Cusp N) (h12 : K12 N) :
    PsiHypotheses N :=
  ⟨p1_proof N, h10, h11a, h11c, h12⟩

/-- K14 with P1 proved: the native value of `Ψ f` is `f`, from K10, K11 and K12. -/
theorem nativeValue_psi_of_K10_K11_K12 (h10 : K10 N) (h11a : K11Arc N) (h11c : K11Cusp N)
    (h12 : K12 N) (f : CuspFormN N) :
    nativeValue N (psi N (psiHypotheses N h10 h11a h11c h12) f) = f :=
  nativeValue_psi N _ f

/-- Route B for `Γ₀(N)`, from K8–K12: the native value `ω ↦ f_ω` is a complex-linear
equivalence between global relative differentials of the complexified modular curve and
weight-two cusp forms on `Γ₀(N)`, with inverse `Ψ`. -/
theorem routeB_linearEquiv (h8 : K8 N) (h9 : K9 N) (h10 : K10 N) (h11a : K11Arc N)
    (h11c : K11Cusp N) (h12 : K12 N) :
    letI := differentialsModule N
    ∃ e : Γ((curveC N).hom.relativeDifferentials, ⊤) ≃ₗ[ℂ] CuspFormN N,
      (∀ ω τ, e ω τ = nativeValue N ω τ) ∧
        ∀ f, e.symm f = psi N (psiHypotheses N h10 h11a h11c h12) f :=
  exists_linearEquiv N _ h8 h9

end ZInQ.Manuscript.RC.CuspFormDifferentials
