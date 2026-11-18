import DirectLevelOneInterpolationV004

/-!
# Actual localized torsion generation for Gamma-one forms

At every level at least three a fixed, explicitly constructed nonzero
level-one denominator multiplies any Gamma-one modular form into a finite
sum of powers of the actual torsion form at (0,1), with genuine level-one
modular forms as coefficients. This is a localized generation theorem;
it does not assert unlocalized principal-product spanning.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm BigOperators

namespace DirectLocalizedTorsionGeneration

open DirectTorsionOrbit DirectOrbitAlgebra DirectOrbitInterpolation DirectLevelOneInterpolation
open ZInQ.Contrib.HeckePrimeRationality

/-- The actual squared denominator at principal level. -/
def squaredDenominator (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    ModularForm ((Gamma N).map (mapGL ℝ)) (2 * orbitWeight N) :=
  ModularForm.mcast (by dsimp [orbitWeight]; ring)
    ((orbitDenominator N hN).mul (orbitDenominator N hN))

/-- Its exact analytic value is the square of the constructed orbit determinant. -/
theorem squaredDenominator_apply (N : ℕ) [NeZero N] (hN : 3 ≤ N) (τ : ℍ) :
    squaredDenominator N hN τ = orbitDenominator N hN τ ^ 2 := by
  simp only [squaredDenominator, ModularForm.mcast_apply, ModularForm.coe_mul, Pi.mul_apply, pow_two]

/-- The fixed denominator, with all level-one modular-form fields constructed. -/
def denominator (N : ℕ) [NeZero N] (hN : 3 ≤ N) : ModularForm 𝒮ℒ (2 * orbitWeight N) :=
  toLevelOne N _ (squaredDenominator N hN)

/-- Its level-one function is exactly the original analytic square. -/
theorem denominator_coe (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    ⇑(denominator N hN) = fun τ : ℍ => orbitDenominator N hN τ ^ 2 := by
  have hs : ∀ γ : SL(2, ℤ),
      ⇑(squaredDenominator N hN) ∣[2 * orbitWeight N] γ = ⇑(squaredDenominator N hN) := by
    intro γ
    simpa only [squaredDenominator, ModularForm.coe_mcast, ModularForm.coe_mul] using
      squared_denominator_slash_invariant N hN γ
  rw [denominator, toLevelOne_coe N _ _ hs]
  funext τ
  exact squaredDenominator_apply N hN τ

/-- Nonvanishing is proved from the actual complete orbit, not supplied by the caller. -/
theorem denominator_ne_zero (N : ℕ) [NeZero N] (hN : 3 ≤ N) : denominator N hN ≠ 0 := by
  have hmul : (orbitDenominator N hN).mul (orbitDenominator N hN) ≠ 0 :=
    ModularForm.mul_ne_zero ⟨(N : ℝ), principal_period N, by exact_mod_cast NeZero.pos N⟩
      (orbitDenominator_ne_zero N hN) (orbitDenominator_ne_zero N hN)
  intro hz
  apply hmul
  apply ModularForm.ext
  intro τ
  have h := congrArg (fun f : ModularForm 𝒮ℒ (2 * orbitWeight N) => f τ) hz
  rw [denominator_coe] at h
  simpa only [ModularForm.zero_apply, ModularForm.coe_mul, Pi.mul_apply, pow_two] using h

/-- The identity torsion entry is the unchanged original analytic torsion function. -/
theorem torsionOrbit_identity_coe (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    ⇑(torsionOrbit N hN (identityIndex N)) = Torsion.torsionLogDerivative N 0 1 := by
  have hdiv : ¬ (N : ℤ) ∣ 1 := fun h => base_good N hN ⟨dvd_zero _, h⟩
  let f := AllLevelForms.torsionForm N (NeZero.pos N) 1 hdiv
  have he : formOrbit N 1 f (identityIndex N) = torsionOrbit N hN (identityIndex N) := by
    apply ModularForm.ext
    intro τ
    rw [formOrbit_coe, DirectTorsionOrbit.torsionOrbit_coe]
    rfl
  rw [← he, formOrbit_identity_coe]
  rfl

/-- Every actual Gamma-one form has the claimed finite localized representation,
with no arithmetic basis, spanning, or Galois-closure premise. -/
theorem localized_generation (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (τ : ℍ) :
    denominator N hN τ * f τ =
      ∑ j : Fin (orbitLength N), levelOneCoefficient N hN k f j τ *
        Torsion.torsionLogDerivative N 0 1 τ ^ (j : ℕ) := by
  have h := squared_denominator_interpolation N hN k f (identityIndex N) τ
  rw [formOrbit_identity_coe, torsionOrbit_identity_coe] at h
  simp_rw [← levelOneCoefficient_coe] at h
  simpa only [denominator_coe] using h

/-- The literal cusp-form specialization keeps the actual Gamma-one object and all integer weights. -/
theorem localized_cusp_generation (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (τ : ℍ) :
    denominator N hN τ * g τ =
      ∑ j : Fin (orbitLength N),
        levelOneCoefficient N hN k (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) j τ *
          Torsion.torsionLogDerivative N 0 1 τ ^ (j : ℕ) :=
  localized_generation N hN k (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) τ

end DirectLocalizedTorsionGeneration
