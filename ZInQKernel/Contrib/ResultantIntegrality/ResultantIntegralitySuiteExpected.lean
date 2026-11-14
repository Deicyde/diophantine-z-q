/-
Resultant integrality tests and exact contract/body checks.
AI-assisted development; no change to the mathematical declarations.
Checking-add resource limits are not trust levels; closure walks are not library replay.
-/

import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.ZMod.Basic
set_option autoImplicit false
open Polynomial
namespace ResultantIntegralitySuiteExpected
def expectedIntegerReflection : Prop :=
  ∀ χ : ℚ[X], χ.Monic →
    (∀ R : ℤ[X], R.natDegree ≤ χ.natDegree →
      ∃ z : ℤ, χ.resultant (R.map (Int.castRingHom ℚ)) = (z : ℚ)) →
    ∃ F : ℤ[X], F.Monic ∧ F.map (Int.castRingHom ℚ) = χ
def strictDegreeReflection : Prop :=
  ∀ χ : ℚ[X], χ.Monic →
    (∀ R : ℤ[X], R.natDegree < χ.natDegree →
      ∃ z : ℤ, χ.resultant (R.map (Int.castRingHom ℚ)) = (z : ℚ)) →
    ∃ F : ℤ[X], F.Monic ∧ F.map (Int.castRingHom ℚ) = χ
def monicityDroppedReflection : Prop :=
  ∀ χ : ℚ[X],
    (∀ R : ℤ[X], R.natDegree ≤ χ.natDegree →
      ∃ z : ℤ, χ.resultant (R.map (Int.castRingHom ℚ)) = (z : ℚ)) →
    ∃ F : ℤ[X], F.Monic ∧ F.map (Int.castRingHom ℚ) = χ
def outputMonicityDroppedReflection : Prop :=
  ∀ χ : ℚ[X], χ.Monic →
    (∀ R : ℤ[X], R.natDegree ≤ χ.natDegree →
      ∃ z : ℤ, χ.resultant (R.map (Int.castRingHom ℚ)) = (z : ℚ)) →
    ∃ F : ℤ[X], F.map (Int.castRingHom ℚ) = χ
def monicTestsOnlyReflection : Prop :=
  ∀ χ : ℚ[X], χ.Monic →
    (∀ R : ℤ[X], R.Monic → R.natDegree ≤ χ.natDegree →
      ∃ z : ℤ, χ.resultant (R.map (Int.castRingHom ℚ)) = (z : ℚ)) →
    ∃ F : ℤ[X], F.Monic ∧ F.map (Int.castRingHom ℚ) = χ
def expectedGenuineIntegerInputs : Prop :=
  ∀ F R : ℤ[X], ∃ z : ℤ,
    (F.map (Int.castRingHom ℚ)).resultant
      (R.map (Int.castRingHom ℚ)) = (z : ℚ)
def expectedPositiveOne : Prop :=
  (1 : ℚ[X]).natDegree = 0 ∧
    ∃ F : ℤ[X], F.Monic ∧ F.map (Int.castRingHom ℚ) = (1 : ℚ[X])
def expectedPositiveX : Prop :=
  (X : ℚ[X]).natDegree = 1 ∧
    ∃ F : ℤ[X], F.Monic ∧ F.map (Int.castRingHom ℚ) = (X : ℚ[X])
def expectedPositiveQuadratic : Prop :=
  (X ^ 2 - 2 : ℚ[X]).natDegree = 2 ∧
    ∃ F : ℤ[X], F.Monic ∧ F.map (Int.castRingHom ℚ) = (X ^ 2 - 2 : ℚ[X])
def expectedPositiveRepeated : Prop :=
  (X ^ 2 : ℚ[X]).natDegree = 2 ∧
    ∃ F : ℤ[X], F.Monic ∧ F.map (Int.castRingHom ℚ) = (X ^ 2 : ℚ[X])
def expectedAdverseLinear : Prop :=
  (X - C (1 / 2 : ℚ)).Monic ∧
    (X : ℤ[X]).natDegree ≤ (X - C (1 / 2 : ℚ)).natDegree ∧
    (X - C (1 / 2 : ℚ)).resultant
      ((X : ℤ[X]).map (Int.castRingHom ℚ)) = (1 / 2 : ℚ) ∧
    (¬ ∃ z : ℤ, (X - C (1 / 2 : ℚ)).resultant
      ((X : ℤ[X]).map (Int.castRingHom ℚ)) = (z : ℚ)) ∧
    ¬ (∀ R : ℤ[X], R.natDegree ≤ (X - C (1 / 2 : ℚ)).natDegree →
      ∃ z : ℤ, (X - C (1 / 2 : ℚ)).resultant
        (R.map (Int.castRingHom ℚ)) = (z : ℚ))
def expectedAdverseQuadratic : Prop :=
  (X ^ 2 + C (1 / 2 : ℚ) * X).Monic ∧
    (X + 1 : ℤ[X]).natDegree ≤ (X ^ 2 + C (1 / 2 : ℚ) * X).natDegree ∧
    (X ^ 2 + C (1 / 2 : ℚ) * X).resultant
      ((X + 1 : ℤ[X]).map (Int.castRingHom ℚ)) = (1 / 2 : ℚ) ∧
    (¬ ∃ z : ℤ, (X ^ 2 + C (1 / 2 : ℚ) * X).resultant
      ((X + 1 : ℤ[X]).map (Int.castRingHom ℚ)) = (z : ℚ)) ∧
    ¬ (∀ R : ℤ[X], R.natDegree ≤ (X ^ 2 + C (1 / 2 : ℚ) * X).natDegree →
      ∃ z : ℤ, (X ^ 2 + C (1 / 2 : ℚ) * X).resultant
        (R.map (Int.castRingHom ℚ)) = (z : ℚ))
def expectedAdverseCubic : Prop :=
  (X ^ 3 + C (1 / 3 : ℚ)).Monic ∧
    (X : ℤ[X]).natDegree ≤ (X ^ 3 + C (1 / 3 : ℚ)).natDegree ∧
    (X ^ 3 + C (1 / 3 : ℚ)).resultant
      ((X : ℤ[X]).map (Int.castRingHom ℚ)) = -(1 / 3 : ℚ) ∧
    (¬ ∃ z : ℤ, (X ^ 3 + C (1 / 3 : ℚ)).resultant
      ((X : ℤ[X]).map (Int.castRingHom ℚ)) = (z : ℚ)) ∧
    ¬ (∀ R : ℤ[X], R.natDegree ≤ (X ^ 3 + C (1 / 3 : ℚ)).natDegree →
      ∃ z : ℤ, (X ^ 3 + C (1 / 3 : ℚ)).resultant
        (R.map (Int.castRingHom ℚ)) = (z : ℚ))
def expectedStrictBoundCounterexample : Prop :=
  (X - C (1 / 2 : ℚ)).natDegree = 1 ∧
    (X - C (1 / 2 : ℚ)).Monic ∧
    (∀ R : ℤ[X], R.natDegree < (X - C (1 / 2 : ℚ)).natDegree →
      ∃ z : ℤ, (X - C (1 / 2 : ℚ)).resultant
        (R.map (Int.castRingHom ℚ)) = (z : ℚ)) ∧
    ¬ ∃ F : ℤ[X], F.map (Int.castRingHom ℚ) = (X - C (1 / 2 : ℚ))
def expectedNoMonicityCounterexample : Prop :=
  (C (1 / 2 : ℚ)).natDegree = 0 ∧
    (¬ (C (1 / 2 : ℚ)).Monic) ∧
    (∀ R : ℤ[X], R.natDegree ≤ (C (1 / 2 : ℚ)).natDegree →
      ∃ z : ℤ, (C (1 / 2 : ℚ)).resultant
        (R.map (Int.castRingHom ℚ)) = (z : ℚ)) ∧
    ¬ ∃ F : ℤ[X], F.map (Int.castRingHom ℚ) = C (1 / 2 : ℚ)
def expectedPositiveReductionDegree : Prop :=
  (2 * X ^ 2 + X : ℤ[X]).map (Int.castRingHom ℚ) =
      C (2 : ℚ) * (X ^ 2 + C (1 / 2 : ℚ) * X) ∧
    (2 * X ^ 2 + X : ℤ[X]).map (Int.castRingHom (ZMod 2)) = (X : (ZMod 2)[X]) ∧
    ((2 * X ^ 2 + X : ℤ[X]).map (Int.castRingHom (ZMod 2))).natDegree = 1 ∧
    0 < ((2 * X ^ 2 + X : ℤ[X]).map (Int.castRingHom (ZMod 2))).natDegree ∧
    ((2 * X ^ 2 + X : ℤ[X]).map (Int.castRingHom (ZMod 2))).natDegree <
      (X ^ 2 + C (1 / 2 : ℚ) * X).natDegree
def expectedConstantReductionDegree : Prop :=
  (3 * X ^ 3 + 1 : ℤ[X]).map (Int.castRingHom ℚ) =
      C (3 : ℚ) * (X ^ 3 + C (1 / 3 : ℚ)) ∧
    (3 * X ^ 3 + 1 : ℤ[X]).map (Int.castRingHom (ZMod 3)) = (1 : (ZMod 3)[X]) ∧
    ((3 * X ^ 3 + 1 : ℤ[X]).map (Int.castRingHom (ZMod 3))).natDegree = 0 ∧
    ((3 * X ^ 3 + 1 : ℤ[X]).map (Int.castRingHom (ZMod 3))).natDegree <
      (X ^ 3 + C (1 / 3 : ℚ)).natDegree
end ResultantIntegralitySuiteExpected
