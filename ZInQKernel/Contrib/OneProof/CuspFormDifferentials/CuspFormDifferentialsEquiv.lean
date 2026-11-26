import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.RouteBCuspAdapter
import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.RouteBK11Arc

/-! Global relative differentials of the complexified modular curve `X₀(N)` and weight-two
cusp forms on `Γ₀(N)` are identified, complex-linearly, by the native value
`ω ↦ (τ ↦ f_ω(τ))`. -/

noncomputable section

open AlgebraicGeometry UpperHalfPlane

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

variable (N : ℕ) [NeZero N]

theorem exists_cuspFormDifferentialsEquiv :
    letI := differentialsModule N
    ∃ e : Γ((curveC N).hom.relativeDifferentials, ⊤) ≃ₗ[ℂ] CuspFormN N,
      ∀ ω τ, e ω τ = nativeValue N ω τ := by
  obtain ⟨e, he, -⟩ := routeB_linearEquiv_of_k11Cusp N (k11Cusp_holds N)
  exact ⟨e, he⟩

/-- Every weight-two cusp form on `Γ₀(N)` is the native value of a global differential. -/
theorem nativeCuspFormMap_surjective :
    letI := differentialsModule N
    Function.Surjective (nativeCuspFormMap N) := by
  letI := differentialsModule N
  obtain ⟨e, he⟩ := exists_cuspFormDifferentialsEquiv N
  intro f
  refine ⟨e.symm f, CuspForm.ext fun τ => ?_⟩
  rw [nativeCuspFormMap_apply, ← he, LinearEquiv.apply_symm_apply]

/-- The native value map, as a complex-linear equivalence between the global relative
differentials of the complexified modular curve and weight-two cusp forms on `Γ₀(N)`. -/
def cuspFormDifferentialsEquiv :
    letI := differentialsModule N
    Γ((curveC N).hom.relativeDifferentials, ⊤) ≃ₗ[ℂ] CuspFormN N :=
  letI := differentialsModule N
  LinearEquiv.ofBijective (nativeCuspFormMap N)
    ⟨nativeCuspFormMap_injective N, nativeCuspFormMap_surjective N⟩

@[simp]
theorem cuspFormDifferentialsEquiv_apply (ω : Γ((curveC N).hom.relativeDifferentials, ⊤))
    (τ : ℍ) : cuspFormDifferentialsEquiv N ω τ = nativeValue N ω τ :=
  rfl

end ZInQ.Manuscript.RC.CuspFormDifferentials

