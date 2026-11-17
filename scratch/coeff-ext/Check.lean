import ZInQKernel.Contrib.OneProof.DSThm965Weak

/-! Verbatim copies of the two targets (coeff-ext), checked equal to the originals by `rfl`. -/

open Polynomial

namespace CoeffExtCheck

def DSThm965WeakCopy : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : ZInQ.Contrib.G9.PkgI4.CF N k),
    0 < N → 2 ≤ k → ZInQ.Contrib.G9.PkgI4.IsNormalizedEigenform g χ →
    ∃ ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ 2, ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
      ρ.UnramifiedAt p ∧ ∃ α β : ZInQ.Contrib.G9.PkgI4.Qbar, ιC α = ZInQ.Contrib.G9.PkgI4.coeff g p ∧
        ιC β = χ (p : ZMod N) * (p : ℂ) ^ (k - 1) ∧
        ∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar) (σ : ZInQ.Contrib.G9.PkgI4.GQ), ZInQ.Contrib.G9.PkgI4.LiesOver v p →
          ZInQ.Contrib.G9.PkgI4.IsArithFrob σ v p →
          (ρ.mat σ).charpoly = X ^ 2 - C (ιL α) * X + C (ιL β) ∨
            aeval (ρ.mat σ) (X ^ 2 - C (ιL α) * X + C (ιL β)) = 0

def DSThm966Copy : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (g : ZInQ.Contrib.G9.PkgI4.CF N 1),
    0 < N → ZInQ.Contrib.G9.PkgI4.IsNormalizedEigenform g χ →
    ∃ ρ : ZInQ.Contrib.G9.PkgI4.GQ →* GL (Fin 2) ℂ, Continuous ρ ∧ (Set.range ρ).Finite ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        (∀ v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar, ZInQ.Contrib.G9.PkgI4.LiesOver v p →
          ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : ZInQ.Contrib.G9.PkgI4.GQ) = 1) ∧
        ∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar) (σ : ZInQ.Contrib.G9.PkgI4.GQ), ZInQ.Contrib.G9.PkgI4.LiesOver v p →
          ZInQ.Contrib.G9.PkgI4.IsArithFrob σ v p →
          (ρ σ : Matrix (Fin 2) (Fin 2) ℂ).trace = ZInQ.Contrib.G9.PkgI4.coeff g p ∧
          (ρ σ : Matrix (Fin 2) (Fin 2) ℂ).det = χ (p : ZMod N)

example : DSThm965WeakCopy = DS965Weak.DSThm965Weak := rfl
example : DSThm966Copy = ZInQ.Contrib.HodgeSplit.DSThm966 := rfl

end CoeffExtCheck
