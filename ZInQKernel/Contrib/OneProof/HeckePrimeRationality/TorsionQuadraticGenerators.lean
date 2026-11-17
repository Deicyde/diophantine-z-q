import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionMuFourierFinite
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionProductBase

/-!
# Quadratic torsion generators at levels at least three

The alternating finite Fourier identities express each actual Weierstrass
torsion value as a fixed complex-linear combination of squares of completed
weight-one torsion values. This constructs weight-two modular forms on the
same principal congruence subgroup, without an analytic modularity premise for
the Weierstrass value. The result does not assert that these forms span the
whole modular-form space or identify them as Eisenstein series.
-/

noncomputable section
set_option autoImplicit false
open Complex UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionQuadraticGenerators

open TorsionWeierstrassData TorsionFourierComparison AllLevelPrincipal AllLevelProducts

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- The quadratic denominator is nonzero exactly in the range used here.
No assertion is made at the exceptional level two. -/
theorem denominator_ne_zero (N : ℕ) (hN : 3 ≤ N) : (N : ℂ) ^ 2 - 4 ≠ 0 := by
  have hr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (N : ℝ) ^ 2 - 4 ≠ 0 := by nlinarith
  exact_mod_cast hn

/-- An explicit quadratic expression for every actual x-value at level at
least three, including the zero torsion class and negative integer labels. -/
theorem xValue_quadratic_formula (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (τ : ℍ) (r s : ℤ) :
    xValue N r s τ =
      ((N : ℂ) ^ 2 * lambdaValue N r s τ ^ 2 +
        2 * ∑ Q : Fin N × Fin N, lambdaValue N (Q.1 : ℕ) (Q.2 : ℕ) τ ^ 2 *
          character N (Q.1 : ℕ) (Q.2 : ℕ) r s) / ((N : ℂ) ^ 2 - 4) := by
  let SX : ℂ := ∑ Q : Fin N × Fin N, xValue N (Q.1 : ℕ) (Q.2 : ℕ) τ *
    character N (Q.1 : ℕ) (Q.2 : ℕ) r s
  let SM : ℂ := ∑ Q : Fin N × Fin N, muValue N (Q.1 : ℕ) (Q.2 : ℕ) τ *
    character N (Q.1 : ℕ) (Q.2 : ℕ) r s
  let SL : ℂ := ∑ Q : Fin N × Fin N, lambdaValue N (Q.1 : ℕ) (Q.2 : ℕ) τ ^ 2 *
    character N (Q.1 : ℕ) (Q.2 : ℕ) r s
  have hx : xValue N r s τ = -SM := by
    simpa only [SM, character, Int.cast_natCast, Fintype.sum_prod_type] using TorsionMuFourier.x_fourier_duality N τ r s
  have hm : muValue N r s τ = -(1 / (N : ℂ) ^ 2) * SX := by
    simpa only [SX, character, Int.cast_natCast, Fintype.sum_prod_type] using TorsionMuFourier.mu_fourier_duality N τ r s
  have hn : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hsx : SX = -(N : ℂ) ^ 2 * muValue N r s τ := by
    field_simp [hn] at hm
    linear_combination hm
  have hsl : SL = SX + 2 * SM := by
    have ht (Q : Fin N × Fin N) : lambdaValue N (Q.1 : ℕ) (Q.2 : ℕ) τ ^ 2 *
        character N (Q.1 : ℕ) (Q.2 : ℕ) r s =
        xValue N (Q.1 : ℕ) (Q.2 : ℕ) τ * character N (Q.1 : ℕ) (Q.2 : ℕ) r s +
          2 * (muValue N (Q.1 : ℕ) (Q.2 : ℕ) τ * character N (Q.1 : ℕ) (Q.2 : ℕ) r s) := by
      unfold muValue
      ring
    change (∑ Q : Fin N × Fin N, _) = _
    simp_rw [ht, Finset.sum_add_distrib, ← Finset.mul_sum]
    rfl
  have hl : lambdaValue N r s τ ^ 2 = xValue N r s τ + 2 * muValue N r s τ := by
    unfold muValue
    ring
  change xValue N r s τ = ((N : ℂ) ^ 2 * lambdaValue N r s τ ^ 2 + 2 * SL) /
    ((N : ℂ) ^ 2 - 4)
  apply (eq_div_iff (denominator_ne_zero N hN)).mpr
  linear_combination -(N : ℂ) ^ 2 * hl - 2 * hsl - 2 * hsx - 4 * hx

/-- The actual completed weight-one torsion form, extended by zero on the
zero label class. -/
def lambdaForm (N : ℕ) (hN : 0 < N) (a b : ℤ) : _root_.ModularForm (ΓP N) 1 :=
  if hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) then
    scale • principalForm N hN a b hg else 0

theorem lambdaForm_apply (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    lambdaForm N hN a b τ = lambdaValue N a b τ := by
  by_cases hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)
  · rw [lambdaForm, dif_pos hg, lambdaValue_of_good N a b τ hg]
    change scale * principalForm N hN a b hg τ = _
    rw [principalForm_apply]
  · have hb : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b := not_not.mp hg
    rw [lambdaForm, dif_neg hg]
    change 0 = scale * TorsionDistributionTwo.reg N a b τ
    rw [TorsionDistributionTwo.reg_of_bad hb, mul_zero]

/-- The actual square, a modular form of weight two at the same level. -/
def lambdaSquare (N : ℕ) (hN : 0 < N) (a b : ℤ) : _root_.ModularForm (ΓP N) 2 :=
  (lambdaForm N hN a b).mul (lambdaForm N hN a b)

theorem lambdaSquare_apply (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    lambdaSquare N hN a b τ = lambdaValue N a b τ ^ 2 := by
  change lambdaForm N hN a b τ * lambdaForm N hN a b τ = _
  rw [lambdaForm_apply]
  ring

/-- The actual x-form is built from the explicit quadratic torsion formula. -/
def xForm (N : ℕ) (hN : 3 ≤ N) (r s : ℤ) : _root_.ModularForm (ΓP N) 2 :=
  (((N : ℂ) ^ 2 - 4)⁻¹) •
    ((N : ℂ) ^ 2 • lambdaSquare N (by omega) r s +
      ∑ Q : Fin N × Fin N, (2 * character N (Q.1 : ℕ) (Q.2 : ℕ) r s) •
        lambdaSquare N (by omega) (Q.1 : ℕ) (Q.2 : ℕ))

theorem xForm_apply (N : ℕ) [NeZero N] (hN : 3 ≤ N) (r s : ℤ) (τ : ℍ) :
    xForm N hN r s τ = xValue N r s τ := by
  have hx := xValue_quadratic_formula N hN τ r s
  unfold xForm
  simp only [smul_apply, smul_eq_mul, add_apply, sum_apply, lambdaSquare_apply]
  have hs : (∑ Q : Fin N × Fin N, (2 * character N (Q.1 : ℕ) (Q.2 : ℕ) r s) *
      lambdaValue N (Q.1 : ℕ) (Q.2 : ℕ) τ ^ 2) =
      2 * ∑ Q : Fin N × Fin N, lambdaValue N (Q.1 : ℕ) (Q.2 : ℕ) τ ^ 2 *
        character N (Q.1 : ℕ) (Q.2 : ℕ) r s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Q _
    ring
  rw [hs, hx]
  ring

/-- The actual μ-form follows from its unchanged quadratic definition. -/
def muForm (N : ℕ) (hN : 3 ≤ N) (a b : ℤ) : _root_.ModularForm (ΓP N) 2 :=
  (1 / 2 : ℂ) • (lambdaSquare N (by omega) a b - xForm N hN a b)

theorem muForm_apply (N : ℕ) [NeZero N] (hN : 3 ≤ N) (a b : ℤ) (τ : ℍ) :
    muForm N hN a b τ = muValue N a b τ := by
  unfold muForm
  simp only [smul_apply, smul_eq_mul, sub_apply, lambdaSquare_apply, xForm_apply]
  unfold muValue
  ring

/-- These bundles share the proved label convention for all integer rows. -/
theorem xForm_shift (N : ℕ) [NeZero N] (hN : 3 ≤ N) (a b m n : ℤ) :
    xForm N hN (a + (N : ℤ) * m) (b + (N : ℤ) * n) = xForm N hN a b := by
  apply _root_.ModularForm.ext
  intro τ
  rw [xForm_apply, xForm_apply, WeierstrassDistributionNat.xValue_shift (by omega)]

theorem muForm_shift (N : ℕ) [NeZero N] (hN : 3 ≤ N) (a b m n : ℤ) :
    muForm N hN (a + (N : ℤ) * m) (b + (N : ℤ) * n) = muForm N hN a b := by
  apply _root_.ModularForm.ext
  intro τ
  rw [muForm_apply, muForm_apply, TorsionMuFourier.muValue_shift]

theorem xForm_zero (N : ℕ) [NeZero N] (hN : 3 ≤ N) : xForm N hN 0 0 = 0 := by
  apply _root_.ModularForm.ext
  intro τ
  rw [xForm_apply, xValue_zero]
  rfl

theorem muForm_zero (N : ℕ) [NeZero N] (hN : 3 ≤ N) : muForm N hN 0 0 = 0 := by
  apply _root_.ModularForm.ext
  intro τ
  rw [muForm_apply, muValue_zero]
  rfl

/-- Each admissible square is a degree-two principal torsion product with its
explicit constant scale. No whole-space spanning assertion is involved. -/
theorem lambdaSquare_eq_product (N : ℕ) (hN : 0 < N) (a b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    lambdaSquare N hN a b = scale ^ 2 • productForm N hN 2 (fun _ => (a, b)) (fun _ => hg) := by
  apply _root_.ModularForm.ext
  intro τ
  rw [lambdaSquare_apply, lambdaValue_of_good N a b τ hg]
  change (scale * Torsion.torsionLogDerivative N a b τ) ^ 2 =
    scale ^ 2 * productForm N hN 2 (fun _ => (a, b)) (fun _ => hg) τ
  have hp := productForm_apply (N := N) hN 2 (fun _ => (a, b))
    (show ∀ _ : Fin 2, AllLevelForms.Good N (a, b) from fun _ => hg) τ
  rw [hp]
  simp only [Fin.prod_univ_two]
  ring

end ZInQ.Contrib.HeckePrimeRationality.TorsionQuadraticGenerators
