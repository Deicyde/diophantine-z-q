import ZInQKernel.Contrib.OneProof.RingClassLattice

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Shimura Complex T5Glue

/-- Verbatim copy of `T5Glue.X0ModuliGalois`. -/
def X0ModuliGaloisCopy : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (g : UpperHalfPlane → ℂ), IsRatModFn N g →
    ∀ (σ : ℂ ≃+* ℂ) (τ τ' : UpperHalfPlane) (μ : ℂ),
      (∀ i < N, ∃ a : Qbar, ιC a = modCoord N τ i) →
      IsConjModel (σ : ℂ →+* ℂ) (pp τ) (pp τ') μ →
      (2 ≤ N → ∃ k : ℕ, 1 ≤ k ∧ k < N ∧
        σ ((pp τ).weierstrassP (1 / N)) = μ ^ 2 * (pp τ').weierstrassP (k / N) ∧
        σ ((pp τ).derivWeierstrassP (1 / N)) = μ ^ 3 * (pp τ').derivWeierstrassP (k / N)) →
      σ (g τ) = g τ'

example : X0ModuliGaloisCopy = T5Glue.X0ModuliGalois := rfl
#check @ιC
#print Qbar
