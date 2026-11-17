import ZInQKernel.Contrib.OneProof.GrossZagierAlgebraic

/-! gamma0-qexp: verbatim copy of the target Prop `ZInQ.GZAlg.Gamma0QExpansion` with its
dependencies (`ZInQ.GZHeegner.IsRatModFnMero`, `ZInQ.GZAlg.HasQExp`, `ZInQ.GZAlg.qPar`,
`ZInQ.GZAlg.X0Field`), and `rfl` checks against the originals. -/

open UpperHalfPlane
open scoped MatrixGroups

noncomputable section

namespace Gamma0QExpCopy

def IsRatModFnMero (N : ℕ) (g : UpperHalfPlane → ℂ) : Prop :=
  (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ∀ τ : UpperHalfPlane, g (γ • τ) = g τ) ∧
  (∀ τ : UpperHalfPlane, MeromorphicAt (g ∘ UpperHalfPlane.ofComplex) (τ : ℂ)) ∧
  (∀ γ : SL(2, ℤ), ∃ k : ℕ,
      (fun τ : UpperHalfPlane => g (γ • τ)) =O[UpperHalfPlane.atImInfty]
        fun τ => Real.exp (2 * Real.pi * k * τ.im)) ∧
  ∃ (k : ℕ) (a : ℕ → ℚ) (T : ℝ), ∀ τ : UpperHalfPlane, T < τ.im →
    HasSum (fun n : ℕ => (a n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * τ) ^ n)
      (Complex.exp (2 * Real.pi * Complex.I * τ) ^ k * g τ)

def qPar (τ : ℍ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * τ)

def HasQExp (X : ℍ → ℂ) (x : LaurentSeries ℚ) : Prop :=
  ∃ T : ℝ, ∀ τ : ℍ, T < τ.im → HasSum (fun m : ℤ => (x.coeff m : ℂ) * qPar τ ^ m) (X τ)

abbrev X0Field (N : ℕ) [NeZero N] : IntermediateField ℚ (LaurentSeries ℚ) :=
  ModularCurve.modularFunctionField N

def Gamma0QExpansion : Prop :=
  ∀ (N : ℕ) [NeZero N] (g : ℍ → ℂ), IsRatModFnMero N g →
    ∀ x : LaurentSeries ℚ, HasQExp g x → x ∈ X0Field N

theorem isRatModFnMero_eq : IsRatModFnMero = ZInQ.GZHeegner.IsRatModFnMero := rfl
theorem qPar_eq : qPar = ZInQ.GZAlg.qPar := rfl
theorem hasQExp_eq : HasQExp = ZInQ.GZAlg.HasQExp := rfl
theorem gamma0QExpansion_eq : Gamma0QExpansion = ZInQ.GZAlg.Gamma0QExpansion := rfl

end Gamma0QExpCopy
