import DirectOrbitAlgebraV003
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Pole-free finite orbit interpolation

Cramer's determinants are built from the actual torsion orbit and the
actual translates of an arbitrary Gamma-one modular form. Multiplication
by the squared orbit denominator gives an exact identity at every
upper-half-plane point. No division by a vanishing analytic value occurs.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm BigOperators

namespace DirectOrbitInterpolation

open DirectTorsionOrbit DirectOrbitAlgebra DirectWeightedDeterminant
open ZInQ.Contrib.HeckePrimeRationality

/-- The actual homogeneous Vandermonde weight. -/
def orbitWeight (N : ℕ) [NeZero N] : ℤ := ∑ j : Fin (orbitLength N), (j : ℤ)

/-- Replacing a column changes its weight by exactly k minus its old column weight. -/
def replacedWeight {r : ℕ} (k : ℤ) (j c : Fin r) : ℤ :=
  (c : ℤ) + if c = j then k - (j : ℤ) else 0

/-- The column replacement is an actual modular form in its stated column weight. -/
def replacedEntry (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (j i c : Fin (orbitLength N)) :
    ModularForm ((Gamma N).map (mapGL ℝ)) (replacedWeight k j c) := by
  classical
  by_cases hc : c = j
  · exact ModularForm.mcast (by simp only [replacedWeight, if_pos hc]; omega)
      (formOrbit N k f i)
  · exact ModularForm.mcast (by simp only [replacedWeight, if_neg hc]; ring)
      ((torsionOrbit N hN i).pow (c : ℕ))

/-- The genuine cofactor determinant, with its exact homogeneous weight. -/
def cofactorForm (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (j : Fin (orbitLength N)) :
    ModularForm ((Gamma N).map (mapGL ℝ)) (k + orbitWeight N - (j : ℤ)) :=
  ModularForm.mcast (by
    classical
    simp only [replacedWeight, Finset.sum_add_distrib]
    simp [orbitWeight]
    ring)
    (determinantForm (replacedWeight k j) (replacedEntry N hN k f j))

/-- Pointwise, this is precisely the ordinary Cramer determinant of the actual orbit data. -/
theorem cofactorForm_apply (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (j : Fin (orbitLength N)) (τ : ℍ) :
    cofactorForm N hN k f j τ =
      (Matrix.vandermonde (fun i => torsionOrbit N hN i τ)).cramer
        (fun i => formOrbit N k f i τ) j := by
  classical
  rw [cofactorForm, ModularForm.mcast_apply, determinantForm_apply, Matrix.cramer_apply]
  apply congrArg Matrix.det
  funext i c
  by_cases hc : c = j
  · simp [replacedEntry, hc, Matrix.updateCol_apply, Matrix.vandermonde_apply]
  · simp [replacedEntry, hc, Matrix.updateCol_apply, Matrix.vandermonde_apply]

/-- Multiplying the cofactor by the original denominator cancels the determinant signs. -/
def coefficientForm (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (j : Fin (orbitLength N)) :
    ModularForm ((Gamma N).map (mapGL ℝ)) (k + 2 * orbitWeight N - (j : ℤ)) :=
  ModularForm.mcast (by dsimp [orbitWeight]; ring)
    ((orbitDenominator N hN).mul (cofactorForm N hN k f j))

/-- The coefficient is built from actual values, not from an asserted interpolation frame. -/
theorem coefficientForm_apply (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (j : Fin (orbitLength N)) (τ : ℍ) :
    coefficientForm N hN k f j τ =
      orbitDenominator N hN τ * cofactorForm N hN k f j τ := rfl

/-- The exact all-point finite-orbit identity, retaining every actual form and denominator. -/
theorem squared_denominator_interpolation (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (i : Fin (orbitLength N)) (τ : ℍ) :
    orbitDenominator N hN τ ^ 2 * formOrbit N k f i τ =
      ∑ j : Fin (orbitLength N), coefficientForm N hN k f j τ *
        torsionOrbit N hN i τ ^ (j : ℕ) := by
  let V := Matrix.vandermonde (fun j => torsionOrbit N hN j τ)
  let b := fun j => formOrbit N k f j τ
  have hrow := congrArg (fun v : Fin (orbitLength N) → ℂ => v i) (Matrix.mulVec_cramer V b)
  have he : (∑ j : Fin (orbitLength N), torsionOrbit N hN i τ ^ (j : ℕ) *
      cofactorForm N hN k f j τ) = orbitDenominator N hN τ * formOrbit N k f i τ := by
    simpa only [V, b, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply,
      ← cofactorForm_apply, orbitDenominator, vandermondeForm_apply,
      Pi.smul_apply, smul_eq_mul] using hrow
  calc
    orbitDenominator N hN τ ^ 2 * formOrbit N k f i τ =
        orbitDenominator N hN τ * (orbitDenominator N hN τ * formOrbit N k f i τ) := by ring
    _ = orbitDenominator N hN τ * (∑ j : Fin (orbitLength N),
        torsionOrbit N hN i τ ^ (j : ℕ) * cofactorForm N hN k f j τ) := by rw [he]
    _ = ∑ j : Fin (orbitLength N), coefficientForm N hN k f j τ *
        torsionOrbit N hN i τ ^ (j : ℕ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [coefficientForm_apply]
      ring

/-- The index of the identity coset in the exact finite enumeration. -/
def identityIndex (N : ℕ) [NeZero N] : Fin (orbitLength N) :=
  orbitEquiv N (QuotientGroup.mk (1 : SL(2, ℤ)))

/-- The identity entry is the original Gamma-one modular form itself. -/
theorem formOrbit_identity_coe (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(formOrbit N k f (identityIndex N)) = ⇑f := by
  have hq : (QuotientGroup.mk (representative N (identityIndex N)) : SL(2, ℤ) ⧸ Gamma1 N) =
      QuotientGroup.mk (1 : SL(2, ℤ)) := by
    simp only [representative, Quotient.out_eq, identityIndex, Equiv.symm_apply_apply]
  have hrel := Quotient.exact hq
  have hm : (representative N (identityIndex N))⁻¹ ∈ Gamma1 N := by
    simpa only [QuotientGroup.leftRel_apply, mul_one] using hrel
  rw [formOrbit_coe]
  exact SlashInvariantFormClass.SL_slash_eq f _ hm

end DirectOrbitInterpolation
