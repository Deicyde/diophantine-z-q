import Mathlib.NumberTheory.ModularForms.JacobiTheta.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-! Real Poisson calculation on a coset of a rectangular ternary lattice.
The form is diagonal in rational quaternion coordinates; the common rectangular
sublattice used for a finite coset presentation need not be the original lattice. -/

noncomputable section

namespace ZInQ.Manuscript.RC.OldStageLaw

open Complex
open UpperHalfPlane hiding I
open scoped Manifold BigOperators Real

/-- The exponential with argument `2π i z t`. -/
def kernel (z : ℂ) (t : ℝ) : ℂ := exp (2 * π * I * z * (t : ℂ))

/-- A line in a lattice coset. `a` includes the square of the step size;
`r` is the offset divided by the step size. -/
def line (a r : ℝ) (z : ℂ) : ℂ :=
  exp (π * I * (r : ℂ) ^ 2 * (2 * (a : ℂ) * z)) *
    jacobiTheta₂ ((r : ℂ) * (2 * (a : ℂ) * z)) (2 * (a : ℂ) * z)

theorem line_hasSum {a : ℝ} (ha : 0 < a) (r : ℝ) (z : ℍ) :
    HasSum (fun n : ℤ => kernel z (a * ((n : ℝ) + r) ^ 2)) (line a r z) := by
  have hi : 0 < (2 * (a : ℂ) * (z : ℂ)).im := by
    rw [← ofReal_ofNat, ← ofReal_mul, im_ofReal_mul]
    exact mul_pos (mul_pos (by norm_num) ha) z.im_pos
  convert (hasSum_jacobiTheta₂_term ((r : ℂ) * (2 * (a : ℂ) * z)) hi).mul_left
    (exp (π * I * (r : ℂ) ^ 2 * (2 * (a : ℂ) * z))) using 1
  · funext n
    simp only [kernel, jacobiTheta₂_term, ← exp_add, ofReal_mul, ofReal_pow, ofReal_add,
      ofReal_intCast]
    congr 1
    ring
  · rfl

theorem line_holo {a : ℝ} (ha : 0 < a) (r : ℝ) : MDiff (fun z : ℍ => line a r z) := by
  intro z
  let f : ℂ → ℂ × ℂ := fun w => ((r : ℂ) * (2 * (a : ℂ) * w), 2 * (a : ℂ) * w)
  have hi : 0 < (f z).2.im := by
    change 0 < (2 * (a : ℂ) * (z : ℂ)).im
    rw [← ofReal_ofNat, ← ofReal_mul, im_ofReal_mul]
    exact mul_pos (mul_pos (by norm_num) ha) z.im_pos
  have hf : DifferentiableAt ℂ f (z : ℂ) := by unfold f; fun_prop
  have hg := (hasFDerivAt_jacobiTheta₂ (f z).1 hi).differentiableAt
  exact (((by fun_prop : DifferentiableAt ℂ
    (fun w : ℂ => exp (π * I * (r : ℂ) ^ 2 * (2 * (a : ℂ) * w))) (z : ℂ))).mul
    (hg.comp (z : ℂ) hf)).mdifferentiableAt.comp z z.mdifferentiable_coe

/-- Poisson summation on an offset line. This form of the Jacobi identity
uses phase `e(nr)`; reindexing the even dual Gaussian also gives `e(-nr)`. -/
theorem line_inversion {a : ℝ} (ha : 0 < a) (r : ℝ) (z : ℍ) :
    line a r (-1 / (z : ℂ)) =
      (1 / (2 * (a : ℂ) * I / (z : ℂ)) ^ (1 / 2 : ℂ)) *
        jacobiTheta₂ (r : ℂ) ((z : ℂ) / (2 * (a : ℂ))) := by
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  let t : ℂ := 2 * (a : ℂ) * (-1 / (z : ℂ))
  have ht : t ≠ 0 := by exact mul_ne_zero (mul_ne_zero two_ne_zero ha') (div_ne_zero (by norm_num) hz)
  have h1 : (r : ℂ) * t / t = (r : ℂ) := mul_div_cancel_right₀ _ ht
  have h2 : -1 / t = (z : ℂ) / (2 * (a : ℂ)) := by dsimp [t]; field_simp
  have h3 : -I * t = 2 * (a : ℂ) * I / (z : ℂ) := by dsimp [t]; ring
  have h4 : -π * I * ((r : ℂ) * t) ^ 2 / t = -(π * I * (r : ℂ) ^ 2 * t) := by
    field_simp
  change exp (π * I * (r : ℂ) ^ 2 * t) * jacobiTheta₂ ((r : ℂ) * t) t = _
  rw [jacobiTheta₂_functional_equation ((r : ℂ) * t) t, h1, h2, h3, h4]
  have hcancel : exp (π * I * (r : ℂ) ^ 2 * t) * exp (-(π * I * (r : ℂ) ^ 2 * t)) = 1 := by
    rw [← exp_add, add_neg_cancel, exp_zero]
  calc
    _ = (1 / (2 * (a : ℂ) * I / (z : ℂ)) ^ (1 / 2 : ℂ)) *
        (exp (π * I * (r : ℂ) ^ 2 * t) * exp (-(π * I * (r : ℂ) ^ 2 * t))) *
        jacobiTheta₂ (r : ℂ) ((z : ℂ) / (2 * (a : ℂ))) := by ring
    _ = _ := by rw [hcancel, mul_one]

/-- A finite linear combination of rectangular ternary lattice cosets. -/
def cosetSum {J : Type*} [Fintype J] (a : Fin 3 → ℝ) (r : J → Fin 3 → ℝ)
    (w : J → ℂ) (z : ℂ) : ℂ :=
  ∑ j, w j * ∏ i, line (a i) (r j i) z

theorem cosetSum_holo {J : Type*} [Fintype J] {a : Fin 3 → ℝ} (ha : ∀ i, 0 < a i)
    (r : J → Fin 3 → ℝ) (w : J → ℂ) : MDiff (fun z : ℍ => cosetSum a r w z) := by
  intro z
  unfold cosetSum
  have hd (j : J) : MDiffAt (fun z : ℍ => w j * ∏ i, line (a i) (r j i) z) z := by
    apply mdifferentiableAt_const.mul
    simp only [Fin.prod_univ_three]
    exact ((line_holo (ha 0) (r j 0) z).mul (line_holo (ha 1) (r j 1) z)).mul
      (line_holo (ha 2) (r j 2) z)
  have he : (fun z : ℍ => ∑ j, w j * ∏ i, line (a i) (r j i) z) =
      ∑ j, (fun z : ℍ => w j * ∏ i, line (a i) (r j i) z) := by
    funext z
    exact (Finset.sum_apply (M := fun _ : ℍ => ℂ) z Finset.univ
      (fun j (u : ℍ) => w j * ∏ i, line (a i) (r j i) u)).symm
  rw [he]
  exact MDifferentiableAt.sum (fun j _ => hd j)

/-- Inversion of the weighted coset sum. The finite Fourier phase of each
coset is retained in its three two-variable Jacobi factors. -/
theorem cosetSum_inversion {J : Type*} [Fintype J] {a : Fin 3 → ℝ} (ha : ∀ i, 0 < a i)
    (r : J → Fin 3 → ℝ) (w : J → ℂ) (z : ℍ) :
    cosetSum a r w (-1 / (z : ℂ)) =
      (∏ i, 1 / (2 * (a i : ℂ) * I / (z : ℂ)) ^ (1 / 2 : ℂ)) *
        ∑ j, w j * ∏ i, jacobiTheta₂ (r j i : ℂ) ((z : ℂ) / (2 * (a i : ℂ))) := by
  simp_rw [cosetSum, line_inversion (ha _), Finset.prod_mul_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

#print axioms line_hasSum
#print axioms line_holo
#print axioms line_inversion
#print axioms cosetSum_holo
#print axioms cosetSum_inversion

end ZInQ.Manuscript.RC.OldStageLaw
