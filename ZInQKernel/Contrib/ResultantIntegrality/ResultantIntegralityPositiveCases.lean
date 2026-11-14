/-
Resultant integrality tests and exact contract/body checks.
AI-assisted development; no change to the mathematical declarations.
Checking-add resource limits are not trust levels; closure walks are not library replay.
-/

import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.RingTheory.Polynomial.Resultant.Basic
namespace ResultantIntegralityCases
open Polynomial
noncomputable section
def IntegerResultantInput (chi : ℚ[X]) : Prop :=
  ∀ R : ℤ[X], R.natDegree ≤ chi.natDegree →
    ∃ z : ℤ, chi.resultant (R.map (Int.castRingHom ℚ)) = (z : ℚ)
def AllIntegerResultants (chi : ℚ[X]) : Prop :=
  ∀ R : ℤ[X],
    ∃ z : ℤ, chi.resultant (R.map (Int.castRingHom ℚ)) = (z : ℚ)
def MonicIntegerLift (chi : ℚ[X]) : Prop :=
  ∃ F : ℤ[X], F.Monic ∧ F.map (Int.castRingHom ℚ) = chi
def PositiveFixture (chi : ℚ[X]) : Prop :=
  chi.Monic ∧ IntegerResultantInput chi ∧ MonicIntegerLift chi
theorem intCastRingHom_injective :
    Function.Injective (Int.castRingHom ℚ) := by
  change Function.Injective (Int.cast : ℤ → ℚ)
  exact Rat.intCast_injective
theorem intMap_natDegree (P : ℤ[X]) :
    (P.map (Int.castRingHom ℚ)).natDegree = P.natDegree := by
  classical
  by_cases hP : P = 0
  · subst P
    simp only [Polynomial.map_zero, Polynomial.natDegree_zero]
  · have hcast : (Int.castRingHom ℚ) P.leadingCoeff ≠ 0 := by
      intro hzero
      exact (Polynomial.leadingCoeff_ne_zero.mpr hP)
        (intCastRingHom_injective
          (hzero.trans (Int.castRingHom ℚ).map_zero.symm))
    exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero
      (Int.castRingHom ℚ) hcast
theorem intMap_resultant (F R : ℤ[X]) :
    (F.map (Int.castRingHom ℚ)).resultant (R.map (Int.castRingHom ℚ)) =
      (F.resultant R : ℚ) := by
  change Polynomial.resultant (F.map (Int.castRingHom ℚ))
      (R.map (Int.castRingHom ℚ))
      (F.map (Int.castRingHom ℚ)).natDegree
      (R.map (Int.castRingHom ℚ)).natDegree =
    (Int.castRingHom ℚ) (Polynomial.resultant F R F.natDegree R.natDegree)
  rw [intMap_natDegree F, intMap_natDegree R]
  exact Polynomial.resultant_map_map F R F.natDegree R.natDegree
    (Int.castRingHom ℚ)
theorem allIntegerResultants_of_intLift (F : ℤ[X]) :
    AllIntegerResultants (F.map (Int.castRingHom ℚ)) := by
  intro R
  exact ⟨F.resultant R, intMap_resultant F R⟩
theorem integerResultantInput_of_intLift (F : ℤ[X]) :
    IntegerResultantInput (F.map (Int.castRingHom ℚ)) := by
  intro R _hR
  exact allIntegerResultants_of_intLift F R
def chiOneZ : ℤ[X] := 1
def chiOneQ : ℚ[X] := 1
theorem chiOneZ_monic : chiOneZ.Monic := by
  change Polynomial.Monic (1 : ℤ[X])
  exact Polynomial.monic_one
theorem chiOneQ_monic : chiOneQ.Monic := by
  change Polynomial.Monic (1 : ℚ[X])
  exact Polynomial.monic_one
theorem chiOneZ_map :
    chiOneZ.map (Int.castRingHom ℚ) = chiOneQ := by
  change (1 : ℤ[X]).map (Int.castRingHom ℚ) = (1 : ℚ[X])
  exact Polynomial.map_one (Int.castRingHom ℚ)
theorem chiOneZ_natDegree : chiOneZ.natDegree = 0 := by
  change Polynomial.natDegree (1 : ℤ[X]) = 0
  exact Polynomial.natDegree_one
theorem chiOneQ_natDegree : chiOneQ.natDegree = 0 := by
  change Polynomial.natDegree (1 : ℚ[X]) = 0
  exact Polynomial.natDegree_one
theorem chiOne_allIntegerResultants : AllIntegerResultants chiOneQ := by
  rw [← chiOneZ_map]
  exact allIntegerResultants_of_intLift chiOneZ
theorem chiOne_integerResultantInput : IntegerResultantInput chiOneQ := by
  intro R _hR
  exact chiOne_allIntegerResultants R
theorem chiOne_monicIntegerLift : MonicIntegerLift chiOneQ :=
  ⟨chiOneZ, chiOneZ_monic, chiOneZ_map⟩
theorem chiOne_positive : PositiveFixture chiOneQ :=
  ⟨chiOneQ_monic, chiOne_integerResultantInput, chiOne_monicIntegerLift⟩
def chiXZ : ℤ[X] := X
def chiXQ : ℚ[X] := X
theorem chiXZ_monic : chiXZ.Monic := by
  change Polynomial.Monic (X : ℤ[X])
  exact Polynomial.monic_X
theorem chiXQ_monic : chiXQ.Monic := by
  change Polynomial.Monic (X : ℚ[X])
  exact Polynomial.monic_X
theorem chiXZ_map :
    chiXZ.map (Int.castRingHom ℚ) = chiXQ := by
  change (X : ℤ[X]).map (Int.castRingHom ℚ) = (X : ℚ[X])
  exact Polynomial.map_X (Int.castRingHom ℚ)
theorem chiXZ_natDegree : chiXZ.natDegree = 1 := by
  change Polynomial.natDegree (X : ℤ[X]) = 1
  exact Polynomial.natDegree_X
theorem chiXQ_natDegree : chiXQ.natDegree = 1 := by
  change Polynomial.natDegree (X : ℚ[X]) = 1
  exact Polynomial.natDegree_X
theorem chiX_allIntegerResultants : AllIntegerResultants chiXQ := by
  rw [← chiXZ_map]
  exact allIntegerResultants_of_intLift chiXZ
theorem chiX_integerResultantInput : IntegerResultantInput chiXQ := by
  intro R _hR
  exact chiX_allIntegerResultants R
theorem chiX_monicIntegerLift : MonicIntegerLift chiXQ :=
  ⟨chiXZ, chiXZ_monic, chiXZ_map⟩
theorem chiX_positive : PositiveFixture chiXQ :=
  ⟨chiXQ_monic, chiX_integerResultantInput, chiX_monicIntegerLift⟩
private theorem two_pos : 0 < (2 : ℕ) :=
  Nat.lt_add_one_of_le
    (Nat.le.intro (n := 0) (m := 1) (k := 1) rfl)
def chiQuadZ : ℤ[X] := X ^ 2 - 2
def chiQuadQ : ℚ[X] := X ^ 2 - 2
theorem chiQuadZ_monic : chiQuadZ.Monic := by
  simpa only [chiQuadZ, Polynomial.Monic, Polynomial.C_ofNat] using
    (Polynomial.leadingCoeff_X_pow_sub_C
      (R := ℤ) (n := 2) (r := (2 : ℤ)) two_pos)
theorem chiQuadQ_monic : chiQuadQ.Monic := by
  simpa only [chiQuadQ, Polynomial.Monic, Polynomial.C_ofNat] using
    (Polynomial.leadingCoeff_X_pow_sub_C
      (R := ℚ) (n := 2) (r := (2 : ℚ)) two_pos)
theorem chiQuadZ_map :
    chiQuadZ.map (Int.castRingHom ℚ) = chiQuadQ := by
  simp only [chiQuadZ, chiQuadQ, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_ofNat]
theorem chiQuadZ_natDegree : chiQuadZ.natDegree = 2 := by
  simpa only [chiQuadZ, Polynomial.C_ofNat] using
    (Polynomial.natDegree_X_pow_sub_C
      (R := ℤ) (n := 2) (r := (2 : ℤ)))
theorem chiQuadQ_natDegree : chiQuadQ.natDegree = 2 := by
  simpa only [chiQuadQ, Polynomial.C_ofNat] using
    (Polynomial.natDegree_X_pow_sub_C
      (R := ℚ) (n := 2) (r := (2 : ℚ)))
theorem chiQuad_allIntegerResultants : AllIntegerResultants chiQuadQ := by
  rw [← chiQuadZ_map]
  exact allIntegerResultants_of_intLift chiQuadZ
theorem chiQuad_integerResultantInput : IntegerResultantInput chiQuadQ := by
  intro R _hR
  exact chiQuad_allIntegerResultants R
theorem chiQuad_monicIntegerLift : MonicIntegerLift chiQuadQ :=
  ⟨chiQuadZ, chiQuadZ_monic, chiQuadZ_map⟩
theorem chiQuad_positive : PositiveFixture chiQuadQ :=
  ⟨chiQuadQ_monic, chiQuad_integerResultantInput, chiQuad_monicIntegerLift⟩
def chiSquareZ : ℤ[X] := X ^ 2
def chiSquareQ : ℚ[X] := X ^ 2
theorem chiSquareZ_monic : chiSquareZ.Monic := by
  change Polynomial.Monic (X ^ 2 : ℤ[X])
  exact Polynomial.monic_X_pow 2
theorem chiSquareQ_monic : chiSquareQ.Monic := by
  change Polynomial.Monic (X ^ 2 : ℚ[X])
  exact Polynomial.monic_X_pow 2
theorem chiSquareZ_map :
    chiSquareZ.map (Int.castRingHom ℚ) = chiSquareQ := by
  change (X ^ 2 : ℤ[X]).map (Int.castRingHom ℚ) = (X ^ 2 : ℚ[X])
  rw [Polynomial.map_pow, Polynomial.map_X]
theorem chiSquareZ_natDegree : chiSquareZ.natDegree = 2 := by
  change Polynomial.natDegree (X ^ 2 : ℤ[X]) = 2
  exact Polynomial.natDegree_X_pow 2
theorem chiSquareQ_natDegree : chiSquareQ.natDegree = 2 := by
  change Polynomial.natDegree (X ^ 2 : ℚ[X]) = 2
  exact Polynomial.natDegree_X_pow 2
theorem chiSquare_allIntegerResultants : AllIntegerResultants chiSquareQ := by
  rw [← chiSquareZ_map]
  exact allIntegerResultants_of_intLift chiSquareZ
theorem chiSquare_integerResultantInput : IntegerResultantInput chiSquareQ := by
  intro R _hR
  exact chiSquare_allIntegerResultants R
theorem chiSquare_monicIntegerLift : MonicIntegerLift chiSquareQ :=
  ⟨chiSquareZ, chiSquareZ_monic, chiSquareZ_map⟩
theorem chiSquare_positive : PositiveFixture chiSquareQ :=
  ⟨chiSquareQ_monic, chiSquare_integerResultantInput, chiSquare_monicIntegerLift⟩
theorem all_positive_fixtures :
    PositiveFixture chiOneQ ∧ PositiveFixture chiXQ ∧
      PositiveFixture chiQuadQ ∧ PositiveFixture chiSquareQ :=
  ⟨chiOne_positive, chiX_positive, chiQuad_positive, chiSquare_positive⟩
end
end ResultantIntegralityCases
