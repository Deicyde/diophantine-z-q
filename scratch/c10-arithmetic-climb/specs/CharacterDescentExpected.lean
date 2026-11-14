import ZInQKernel.HDecomp.C10.C10
import ZInQKernel.HDecomp.Descent.Chi

/-!
Independent full target statements for fixed-place coefficient-character descent.
These definitions do not assert a proof, B2 cochain construction or C10 closure.
-/

namespace ClimbCharacterExpected

/-- The same complex character is recovered through the fixed place, with its order unchanged. -/
def FixedPlaceDescent : Prop :=
  ∀ (n : ℕ) [NeZero n] (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ)
    (χ : DirichletCharacter ℂ n),
    ∃ χ₀ : DirichletCharacter GlueC10.Qbar n,
      (∀ a : ZMod n, ρ (χ₀ a) = χ a) ∧ orderOf χ₀ = orderOf χ

/-- Oddness is about the recovered actual character, not a newly chosen incompatible place. -/
def FixedPlaceOddness : Prop :=
  ∀ (n : ℕ) [NeZero n] (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ)
    (χ : DirichletCharacter ℂ n),
    χ (-1) = -1 →
      ∃ χ₀ : DirichletCharacter GlueC10.Qbar n,
        (∀ a : ZMod n, ρ (χ₀ a) = χ a) ∧ χ₀ (-1) = -1 ∧
        orderOf χ₀ = orderOf χ

/-- The existing GlueDescent character, with its original level and prime-supported order bound. -/
def ActualGlueCharacter : Prop :=
  ∀ (T Tm : Finset ℕ), (∀ p ∈ T, p.Prime) → Tm ⊆ T →
    ∀ (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ),
      ∃ χ₀ : DirichletCharacter GlueC10.Qbar (GlueDescent.chiLevel Tm),
        (∀ a : ZMod (GlueDescent.chiLevel Tm), ρ (χ₀ a) = GlueDescent.chi Tm a) ∧
        orderOf χ₀ = orderOf (GlueDescent.chi Tm) ∧
        orderOf χ₀ ≤ 2 * ∏ p ∈ T.filter (· ≠ 2), (p - 1)

end ClimbCharacterExpected
