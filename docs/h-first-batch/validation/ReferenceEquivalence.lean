import ZInQKernel.Targets.H.T13
import ZInQKernel.Targets.H.T17
import ZInQKernel.Targets.H.T19
import ZInQKernel.Targets.H.T21

/-! Reference-equivalence checks for the first batch. These do not prove any leaf.
The quoted expressions preserve the frozen PR #41 statement bodies exactly.
-/

open scoped MatrixGroups
open NumberField

namespace FirstHBatch.Reference

def T13 : Prop :=
  ∀ (K A B : Type) [Field K] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] [Ring B] [Algebra K B] [IsSimpleRing B] [FiniteDimensional K B]
    (f g : B →ₐ[K] A), ∃ x : Aˣ, ∀ b, g b = (x : A) * f b * ((x⁻¹ : Aˣ) : A)

def T17 : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
    (∀ σ τ : L ≃ₐ[ℚ] L, σ * τ = τ * σ) →
    ∃ n : ℕ+, Nonempty (L →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ)

def T19 : Prop :=
  ∀ (G : Type) [Group G] (E : Type) [Field E] [CharZero E] (n : ℕ)
    (ρ₁ ρ₂ : G →* GL (Fin n) E),
    (∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
    (∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
    (∀ g, Matrix.trace (ρ₁ g : Matrix (Fin n) (Fin n) E) =
      Matrix.trace (ρ₂ g : Matrix (Fin n) (Fin n) E)) →
    ∃ P : GL (Fin n) E, ∀ g, ρ₂ g = P * ρ₁ g * P⁻¹

def T21 : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (p : ℕ), p.Prime → ∀ (P : Ideal (𝓞 L)) [P.IsPrime],
    P.LiesOver (Ideal.span {(p : ℤ)}) →
    ¬ P ^ (P.ramificationIdx ℤ - 1 + P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + 1)
      ∣ differentIdeal ℤ (𝓞 L)

example : ZInQ.Targets.H.T13 ↔ T13 := Iff.rfl
example : ZInQ.Targets.H.T17 ↔ T17 := Iff.rfl
example : ZInQ.Targets.H.T19 ↔ T19 := Iff.rfl
example : ZInQ.Targets.H.T21 ↔ T21 := Iff.rfl

end FirstHBatch.Reference

#check ZInQ.Targets.H.T13
#check ZInQ.Targets.H.T17
#check ZInQ.Targets.H.T19
#check ZInQ.Targets.H.T21
#print axioms ZInQ.Targets.H.T13
#print axioms ZInQ.Targets.H.T17
#print axioms ZInQ.Targets.H.T19
#print axioms ZInQ.Targets.H.T21
