import ZInQKernel.Contrib.OneProof.SZThm33
import ZInQKernel.Contrib.AbVarBC.Points

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open ReductSplit (TΩ galTΩ)
open ZInQ.Contrib.AbVarBC

namespace SZRaynaud

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  (A : PkgI3.AbVar K) (E : IntermediateField K Ω) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The same geometric point system before and after extending the ground field. -/
def intermediateTateEquiv : TΩ (A.baseChange E) Ω ℓ ≃ₗ[ℤ_[ℓ]] TΩ A Ω ℓ :=
  let e := bcPt (L := E) A Ω
  let f := PkgI3.Tate.map e.toMonoidHom.toAdditive (ℓ := ℓ)
  LinearEquiv.ofBijective f ⟨by
    intro x y h
    apply Subtype.ext
    funext n
    apply Additive.toMul.injective
    apply e.injective
    exact congrArg (fun t : TΩ A Ω ℓ => Additive.toMul (t.1 n)) h,
    by
      intro y
      refine ⟨PkgI3.Tate.map e.symm.toMonoidHom.toAdditive y, ?_⟩
      apply Subtype.ext
      funext n
      exact congrArg Additive.ofMul (e.apply_symm_apply _)⟩

theorem intermediateTateEquiv_action (σ : Ω ≃ₐ[E] Ω) (x : TΩ (A.baseChange E) Ω ℓ) :
    intermediateTateEquiv A E ℓ (galTΩ (A.baseChange E) ℓ σ x) =
      galTΩ A ℓ (σ.restrictScalars K) (intermediateTateEquiv A E ℓ x) := by
  apply Subtype.ext
  funext n
  exact congrArg Additive.ofMul (bcPt_galAct A Ω σ (Additive.toMul (x.1 n)))

/-- Changing the ground field while retaining the chosen algebraic closure
does not change the rational Tate space. -/
abbrev intermediateRationalTateEquiv :
    VΩ (A.baseChange E) Ω ℓ ≃ₗ[ℚ_[ℓ]] VΩ A Ω ℓ :=
  LinearEquiv.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _ (intermediateTateEquiv A E ℓ)

theorem intermediateRationalTateEquiv_action (σ : Ω ≃ₐ[E] Ω)
    (x : VΩ (A.baseChange E) Ω ℓ) :
    intermediateRationalTateEquiv A E ℓ (galVΩ (A.baseChange E) ℓ σ x) =
      galVΩ A ℓ (σ.restrictScalars K) (intermediateRationalTateEquiv A E ℓ x) := by
  let e := (intermediateTateEquiv A E ℓ).toLinearMap
  have h : e.comp (galTΩ (A.baseChange E) ℓ σ) = (galTΩ A ℓ (σ.restrictScalars K)).comp e :=
    LinearMap.ext (intermediateTateEquiv_action A E ℓ σ)
  have h' := congrArg (LinearMap.baseChange ℚ_[ℓ]) h
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at h'
  exact LinearMap.congr_fun h' x

end SZRaynaud
