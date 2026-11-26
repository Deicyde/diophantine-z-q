import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.Assembly
import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.NativeCuspForm

/-! The linear map from global differentials to cusp forms and its injectivity discharge the
first two hypotheses of the assembled equivalence. What remains are the closed-point,
valuation and regularity statements. -/

noncomputable section

open AlgebraicGeometry UpperHalfPlane

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

variable (N : ℕ) [NeZero N]

theorem k8_holds : K8 N :=
  ⟨nativeCuspFormMap N, fun _ _ => rfl⟩

theorem k9_holds : K9 N :=
  fun ω h => eq_zero_of_nativeValue_fun_eq_zero N ω h

/-- Global differentials of the complexified modular curve and weight-two cusp forms on
`Γ₀(N)` are identified by the native value, given the closed-point, valuation and
regularity statements. -/
theorem routeB_linearEquiv_of_points_regularity (h10 : K10 N) (h11a : K11Arc N)
    (h11c : K11Cusp N) (h12 : K12 N) :
    letI := differentialsModule N
    ∃ e : Γ((curveC N).hom.relativeDifferentials, ⊤) ≃ₗ[ℂ] CuspFormN N,
      (∀ ω τ, e ω τ = nativeValue N ω τ) ∧
        ∀ f, e.symm f = psi N (psiHypotheses N h10 h11a h11c h12) f :=
  routeB_linearEquiv N (k8_holds N) (k9_holds N) h10 h11a h11c h12

end ZInQ.Manuscript.RC.CuspFormDifferentials

