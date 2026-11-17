import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelThetaNonvanishing
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# The completed odd theta function

For `τ` in the upper half-plane and `z : ℂ` put
`H τ z = exp(π i z) θ(z + (τ + 1)/2, τ)`, with `θ = jacobiTheta₂` (Mathlib's `θ₃` normalization).
Up to a nonzero constant this is the odd Jacobi theta function `θ₁`.

Main results.
* Holomorphy: `H τ` has derivative `Hder τ z = exp(π i z) (π i θ(w, τ) + θ'(w, τ))`,
  `w = z + (τ + 1)/2` (`hasDerivAt_H`), and `(z, τ) ↦ H` is jointly complex differentiable.
* `H τ (z + 1) = -H τ z`, `H τ (z + τ) = -exp(-π i τ - 2π i z) H τ z`, `H τ (-z) = -H τ z`,
  `H τ 0 = 0`.
* At a torsion point `u = (a τ + b)/N` with `(a, b)` not both divisible by `N`, `H τ u ≠ 0`, and
  the torsion logarithmic derivative is
  `torsionLogDerivative N a b τ = a/N + Hder τ u / (2π i H τ u)`.
-/

noncomputable section

open Complex
open scoped Real UpperHalfPlane

namespace ZInQ.Contrib.HeckePrimeRationality.CompletedTheta

/-- The completed odd theta function. -/
def H (τ : ℍ) (z : ℂ) : ℂ := cexp (π * I * z) * jacobiTheta₂ (z + ((τ : ℂ) + 1) / 2) τ

/-- Its `z`-derivative. -/
def Hder (τ : ℍ) (z : ℂ) : ℂ :=
  cexp (π * I * z) * (π * I * jacobiTheta₂ (z + ((τ : ℂ) + 1) / 2) τ +
    jacobiTheta₂' (z + ((τ : ℂ) + 1) / 2) τ)

/-! ### Holomorphy -/

theorem hasDerivAt_H (τ : ℍ) (z : ℂ) : HasDerivAt (H τ) (Hder τ z) z := by
  set c : ℂ := ((τ : ℂ) + 1) / 2
  have hθ : HasDerivAt (fun x => jacobiTheta₂ (x + c) τ) (jacobiTheta₂' (z + c) τ) z :=
    HasDerivAt.comp_add_const z c (hasDerivAt_jacobiTheta₂_fst (z + c) τ.im_pos)
  have he : HasDerivAt (fun x : ℂ => cexp (π * I * x)) (cexp (π * I * z) * (π * I)) z := by
    have h := ((hasDerivAt_id z).const_mul (π * I : ℂ)).cexp
    simpa using h
  refine (he.mul hθ).congr_deriv ?_
  simp only [Hder, c]
  ring

theorem deriv_H (τ : ℍ) (z : ℂ) : deriv (H τ) z = Hder τ z := (hasDerivAt_H τ z).deriv

theorem differentiable_H (τ : ℍ) : Differentiable ℂ (H τ) := fun z =>
  (hasDerivAt_H τ z).differentiableAt

/-- Joint holomorphy in `(z, τ)` on `ℂ × {Im τ > 0}`. -/
theorem differentiableAt_H_joint {z τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ => cexp (π * I * p.1) * jacobiTheta₂ (p.1 + (p.2 + 1) / 2) p.2)
      (z, τ) := by
  have h1 : DifferentiableAt ℂ (fun p : ℂ × ℂ => (p.1 + (p.2 + 1) / 2, p.2)) (z, τ) := by
    fun_prop
  have h2 : DifferentiableAt ℂ (fun p : ℂ × ℂ => jacobiTheta₂ (p.1 + (p.2 + 1) / 2) p.2) (z, τ) :=
    DifferentiableAt.comp (f := fun p : ℂ × ℂ => (p.1 + (p.2 + 1) / 2, p.2))
      (g := fun q : ℂ × ℂ => jacobiTheta₂ q.1 q.2) (z, τ)
      (hasFDerivAt_jacobiTheta₂ (z + (τ + 1) / 2) hτ).differentiableAt h1
  have h3 : DifferentiableAt ℂ (fun p : ℂ × ℂ => cexp (π * I * p.1)) (z, τ) := by fun_prop
  exact h3.mul h2

/-! ### Quasi-periodicity and parity -/

theorem exp_eq_neg_of {X Y : ℂ} (n : ℤ) (h : X = Y + π * I + n * (2 * π * I)) :
    cexp X = -cexp Y := by
  rw [h, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I,
    Complex.exp_int_mul_two_pi_mul_I]
  ring

theorem H_add_one (τ : ℍ) (z : ℂ) : H τ (z + 1) = -H τ z := by
  unfold H
  have hw : z + 1 + ((τ : ℂ) + 1) / 2 = (z + ((τ : ℂ) + 1) / 2) + 1 := by ring
  rw [hw, jacobiTheta₂_add_left, exp_eq_neg_of 0 (show π * I * (z + 1) = π * I * z + π * I +
    ((0 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring)]
  ring

theorem H_add_tau (τ : ℍ) (z : ℂ) :
    H τ (z + τ) = -cexp (-π * I * τ - 2 * π * I * z) * H τ z := by
  unfold H
  set w := z + ((τ : ℂ) + 1) / 2 with hw
  have hw' : z + (τ : ℂ) + ((τ : ℂ) + 1) / 2 = w + τ := by rw [hw]; ring
  rw [hw', jacobiTheta₂_add_left']
  have he : cexp (π * I * (z + τ)) * cexp (-π * I * (τ + 2 * w)) =
      -(cexp (-π * I * τ - 2 * π * I * z) * cexp (π * I * z)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    refine exp_eq_neg_of (-1) ?_
    rw [hw]; push_cast; ring
  linear_combination (jacobiTheta₂ w τ) * he

theorem H_neg (τ : ℍ) (z : ℂ) : H τ (-z) = -H τ z := by
  unfold H
  set x := z - ((τ : ℂ) + 1) / 2 with hx
  have h1 : -z + ((τ : ℂ) + 1) / 2 = -x := by rw [hx]; ring
  have h2 : z + ((τ : ℂ) + 1) / 2 = (x + τ) + ((1 : ℤ) : ℂ) := by rw [hx]; push_cast; ring
  rw [h1, jacobiTheta₂_neg_left, h2, ThetaFive.jacobiTheta₂_add_int_left, jacobiTheta₂_add_left']
  have he : cexp (π * I * z) * cexp (-π * I * (τ + 2 * x)) = -cexp (π * I * -z) := by
    rw [← Complex.exp_add]
    refine exp_eq_neg_of 0 ?_
    rw [hx]; push_cast; ring
  linear_combination (jacobiTheta₂ x τ) * he

theorem H_zero (τ : ℍ) : H τ 0 = 0 := by
  have h := H_neg τ 0
  rw [neg_zero] at h
  linear_combination h / 2

/-! ### Torsion points -/

/-- The level-`N` torsion point `(a τ + b)/N`. -/
def torsionPoint (N : ℕ) (a b : ℤ) (τ : ℍ) : ℂ := ((a : ℂ) * τ + b) / N

theorem shiftedPoint_eq (N : ℕ) (a b : ℤ) (τ : ℍ) :
    Torsion.shiftedPoint N a b τ = torsionPoint N a b τ + ((τ : ℂ) + 1) / 2 := rfl

theorem H_torsion (N : ℕ) (a b : ℤ) (τ : ℍ) :
    H τ (torsionPoint N a b τ) =
      cexp (π * I * torsionPoint N a b τ) * jacobiTheta₂ (Torsion.shiftedPoint N a b τ) τ := rfl

/-- `H` does not vanish at nonzero torsion points. -/
theorem H_torsion_ne_zero (N : ℕ) (hN : 0 < N) (τ : ℍ) (a b : ℤ)
    (h : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) : H τ (torsionPoint N a b τ) ≠ 0 := by
  rw [H_torsion]
  exact mul_ne_zero (Complex.exp_ne_zero _)
    (AllLevelTheta.jacobiTheta₂_shiftedPoint_ne_zero N hN τ a b h)

/-- **The torsion logarithmic derivative through `H`**:
`torsionLogDerivative N a b τ = a/N + H'(u) / (2π i H(u))`, `u = (a τ + b)/N`. -/
theorem torsionLogDerivative_eq (N : ℕ) (hN : 0 < N) (τ : ℍ) (a b : ℤ)
    (h : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    Torsion.torsionLogDerivative N a b τ =
      (a : ℂ) / N + Hder τ (torsionPoint N a b τ) /
        (2 * π * I * H τ (torsionPoint N a b τ)) := by
  have hθ := AllLevelTheta.jacobiTheta₂_shiftedPoint_ne_zero N hN τ a b h
  have he := Complex.exp_ne_zero (π * I * torsionPoint N a b τ)
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold Torsion.torsionLogDerivative
  rw [H_torsion]
  unfold Hder
  rw [← shiftedPoint_eq]
  generalize jacobiTheta₂ (Torsion.shiftedPoint N a b τ) τ = A at hθ ⊢
  generalize jacobiTheta₂' (Torsion.shiftedPoint N a b τ) τ = B
  generalize cexp (π * I * torsionPoint N a b τ) = E at he ⊢
  field_simp
  ring

/-- The same formula with the actual derivative `deriv (H τ)`. -/
theorem torsionLogDerivative_eq_deriv (N : ℕ) (hN : 0 < N) (τ : ℍ) (a b : ℤ)
    (h : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    Torsion.torsionLogDerivative N a b τ =
      (a : ℂ) / N + deriv (H τ) (torsionPoint N a b τ) /
        (2 * π * I * H τ (torsionPoint N a b τ)) := by
  rw [deriv_H]; exact torsionLogDerivative_eq N hN τ a b h

end ZInQ.Contrib.HeckePrimeRationality.CompletedTheta
