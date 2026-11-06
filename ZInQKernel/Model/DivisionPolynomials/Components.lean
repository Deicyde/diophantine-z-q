import ZInQKernel.Model.DivisionPolynomials.MulByN

/-!
# Evaluating the component polynomials

The component polynomial `Ψ_{n,c} ∈ ℤ[x₀, x₁, y₀, y₁]` evaluated at rationals `(x₀, x₁, y₀, y₁)` is
the `s^c`-coefficient of `ψ_n(x₀ + x₁ s, y₀ + y₁ s) ∈ K₀` for `A = -d²` (`psiComponent_eval`).
-/

namespace ZInQ.Syntax

open Polynomial

lemma normDiv_eval {R : Type*} [CommRing R] (B z : R) (k : ℕ) : (normDiv B k).eval z =
    preNormEDS' ((divD0 B).eval z) ((divF3 B).eval z) ((divF4 B).eval z) k := by
  rw [normDiv, ← coe_evalRingHom, map_preNormEDS']

/-- `ψ_n` commutes with ring homomorphisms. -/
lemma map_psiEval {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (A : R) (n : ℤ)
    (x y : R) : f (psiEval A n x y) = psiEval (f A) n (f x) (f y) := by
  rw [psiEval_eq, psiEval_eq, normDiv_eval A x, normDiv_eval (f A) (f x)]
  simp only [map_mul, map_intCast, map_preNormEDS', apply_ite f, map_one, map_ofNat]
  simp [divD0, divF3, divF4, map_ofNat]

/-- Componentwise evaluation `ℤ[x₀, x₁, y₀, y₁][s]/(s² - 2) → K₀` at `v ∈ ℚ⁴`. -/
noncomputable def componentEval (v : Fin 4 → ℚ) : ComponentRing →+* K0 where
  toFun z := ⟨MvPolynomial.eval₂ (Int.castRingHom ℚ) v z.re,
    MvPolynomial.eval₂ (Int.castRingHom ℚ) v z.im⟩
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' a b := by ext <;> simp [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_add]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp [MvPolynomial.eval₂_add]

lemma componentEval_re (v : Fin 4 → ℚ) (z : ComponentRing) :
    (componentEval v z).re = MvPolynomial.eval₂ (Int.castRingHom ℚ) v z.re := rfl

lemma componentEval_im (v : Fin 4 → ℚ) (z : ComponentRing) :
    (componentEval v z).im = MvPolynomial.eval₂ (Int.castRingHom ℚ) v z.im := rfl

lemma componentEval_componentA (v : Fin 4 → ℚ) : componentEval v componentA = genA := by
  rw [genA_eq]; ext <;> simp [componentEval, componentA]

/-- `Ψ_{n,c}(x₀, x₁, y₀, y₁)` is the coefficient of `s^c` in `ψ_n(x₀ + x₁ s, y₀ + y₁ s)`, where
`ψ_n` are the division polynomials of `E : y² = x³ - d²x` over `K₀`. -/
theorem psiComponent_eval (n : ℤ) (c : Fin 2) (v : Fin 4 → ℚ) :
    MvPolynomial.eval₂ (Int.castRingHom ℚ) v (psiComponent n c) =
      ![(psiEval genA n ⟨v 0, v 1⟩ ⟨v 2, v 3⟩).re, (psiEval genA n ⟨v 0, v 1⟩ ⟨v 2, v 3⟩).im] c := by
  have e := map_psiEval (componentEval v) componentA n ⟨.X 0, .X 1⟩ ⟨.X 2, .X 3⟩
  rw [componentEval_componentA] at e
  have ex : componentEval v ⟨.X 0, .X 1⟩ = ⟨v 0, v 1⟩ := by ext <;> simp [componentEval]
  have ey : componentEval v ⟨.X 2, .X 3⟩ = ⟨v 2, v 3⟩ := by ext <;> simp [componentEval]
  rw [ex, ey] at e
  fin_cases c
  · simp [psiComponent, ← e, componentEval_re]
  · simp [psiComponent, ← e, componentEval_im]

end ZInQ.Syntax
