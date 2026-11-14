/-
Resultant integrality tests and exact contract/body checks.
AI-assisted development; no change to the mathematical declarations.
Checking-add resource limits are not trust levels; closure walks are not library replay.
-/

import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.ZMod.Basic
open Polynomial
namespace ResultantIntegralityReductionCases
noncomputable def F2 : ℤ[X] := 2 * X ^ 2 + X
noncomputable def F3 : ℤ[X] := 3 * X ^ 3 + 1
noncomputable def chi2 : ℚ[X] := X ^ 2 + C (1 / 2 : ℚ) * X
noncomputable def chi3 : ℚ[X] := X ^ 3 + C (1 / 3 : ℚ)
theorem rat_two_mul_half : (2 : ℚ) * (1 / 2) = 1 :=
  mul_one_div_cancel (two_ne_zero : (2 : ℚ) ≠ 0)
theorem rat_three_mul_third : (3 : ℚ) * (1 / 3) = 1 :=
  mul_one_div_cancel (three_ne_zero : (3 : ℚ) ≠ 0)
theorem rat_half_ne_zero : (1 / 2 : ℚ) ≠ 0 := fun h0 =>
  one_ne_zero (rat_two_mul_half.symm.trans (by rw [h0, mul_zero]))
theorem zmod2_two_eq_zero : (2 : ZMod 2) = 0 :=
  (Nat.cast_ofNat : ((OfNat.ofNat 2 : ℕ) : ZMod 2) = OfNat.ofNat 2).symm.trans
    (ZMod.natCast_self 2)
theorem zmod3_three_eq_zero : (3 : ZMod 3) = 0 :=
  (Nat.cast_ofNat : ((OfNat.ofNat 3 : ℕ) : ZMod 3) = OfNat.ofNat 3).symm.trans
    (ZMod.natCast_self 3)
theorem zmod2X_two_eq_zero : (2 : (ZMod 2)[X]) = 0 :=
  calc (2 : (ZMod 2)[X]) = C (2 : ZMod 2) := (C_ofNat 2).symm
    _ = C 0 := congrArg C zmod2_two_eq_zero
    _ = 0 := C_0
theorem zmod3X_three_eq_zero : (3 : (ZMod 3)[X]) = 0 :=
  calc (3 : (ZMod 3)[X]) = C (3 : ZMod 3) := (C_ofNat 3).symm
    _ = C 0 := congrArg C zmod3_three_eq_zero
    _ = 0 := C_0
theorem C_two_mul_C_half : C (2 : ℚ) * C (1 / 2 : ℚ) = 1 :=
  calc C (2 : ℚ) * C (1 / 2 : ℚ) = C ((2 : ℚ) * (1 / 2)) := C_mul.symm
    _ = C 1 := congrArg C rat_two_mul_half
    _ = 1 := C_1
theorem C_three_mul_C_third : C (3 : ℚ) * C (1 / 3 : ℚ) = 1 :=
  calc C (3 : ℚ) * C (1 / 3 : ℚ) = C ((3 : ℚ) * (1 / 3)) := C_mul.symm
    _ = C 1 := congrArg C rat_three_mul_third
    _ = 1 := C_1
theorem F2_map_rat_expand : F2.map (Int.castRingHom ℚ) = 2 * X ^ 2 + X := by
  simp only [F2, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat]
theorem F3_map_rat_expand : F3.map (Int.castRingHom ℚ) = 3 * X ^ 3 + 1 := by
  simp only [F3, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat, Polynomial.map_one]
theorem F2_map_rat :
    F2.map (Int.castRingHom ℚ) = C (2 : ℚ) * (X ^ 2 + C (1 / 2 : ℚ) * X) :=
  have h2 : (2 : ℚ[X]) = C (2 : ℚ) := (C_ofNat 2).symm
  calc F2.map (Int.castRingHom ℚ) = 2 * X ^ 2 + X := F2_map_rat_expand
    _ = C (2 : ℚ) * X ^ 2 + X := congrArg (fun t : ℚ[X] => t * X ^ 2 + X) h2
    _ = C (2 : ℚ) * X ^ 2 + 1 * X :=
      congrArg (fun t : ℚ[X] => C (2 : ℚ) * X ^ 2 + t) (one_mul (X : ℚ[X])).symm
    _ = C (2 : ℚ) * X ^ 2 + C (2 : ℚ) * C (1 / 2 : ℚ) * X :=
      congrArg (fun t : ℚ[X] => C (2 : ℚ) * X ^ 2 + t * X) C_two_mul_C_half.symm
    _ = C (2 : ℚ) * X ^ 2 + C (2 : ℚ) * (C (1 / 2 : ℚ) * X) :=
      congrArg (fun t : ℚ[X] => C (2 : ℚ) * X ^ 2 + t) (mul_assoc (C (2 : ℚ)) (C (1 / 2 : ℚ)) X)
    _ = C (2 : ℚ) * (X ^ 2 + C (1 / 2 : ℚ) * X) :=
      (mul_add (C (2 : ℚ)) (X ^ 2) (C (1 / 2 : ℚ) * X)).symm
theorem F3_map_rat :
    F3.map (Int.castRingHom ℚ) = C (3 : ℚ) * (X ^ 3 + C (1 / 3 : ℚ)) :=
  have h3 : (3 : ℚ[X]) = C (3 : ℚ) := (C_ofNat 3).symm
  calc F3.map (Int.castRingHom ℚ) = 3 * X ^ 3 + 1 := F3_map_rat_expand
    _ = C (3 : ℚ) * X ^ 3 + 1 := congrArg (fun t : ℚ[X] => t * X ^ 3 + 1) h3
    _ = C (3 : ℚ) * X ^ 3 + C (3 : ℚ) * C (1 / 3 : ℚ) :=
      congrArg (fun t : ℚ[X] => C (3 : ℚ) * X ^ 3 + t) C_three_mul_C_third.symm
    _ = C (3 : ℚ) * (X ^ 3 + C (1 / 3 : ℚ)) :=
      (mul_add (C (3 : ℚ)) (X ^ 3) (C (1 / 3 : ℚ))).symm
theorem F2_map_rat_eq_C_mul_chi2 : F2.map (Int.castRingHom ℚ) = C (2 : ℚ) * chi2 := by
  unfold chi2
  exact F2_map_rat
theorem F3_map_rat_eq_C_mul_chi3 : F3.map (Int.castRingHom ℚ) = C (3 : ℚ) * chi3 := by
  unfold chi3
  exact F3_map_rat
theorem F2_map_zmod2 : F2.map (Int.castRingHom (ZMod 2)) = X := by
  simp only [F2, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat, zmod2X_two_eq_zero, zero_mul, zero_add]
theorem F3_map_zmod3 : F3.map (Int.castRingHom (ZMod 3)) = 1 := by
  simp only [F3, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat, Polynomial.map_one, zmod3X_three_eq_zero, zero_mul, zero_add]
theorem F2_mod2_natDegree : (F2.map (Int.castRingHom (ZMod 2))).natDegree = 1 := by
  letI : Nontrivial (ZMod 2) := ZMod.nontrivial_iff.mpr (by decide)
  rw [F2_map_zmod2, natDegree_X]
theorem F3_mod3_natDegree : (F3.map (Int.castRingHom (ZMod 3))).natDegree = 0 := by
  rw [F3_map_zmod3, natDegree_one]
theorem chi2_natDegree : chi2.natDegree = 2 := by
  have h1 : (C (1 / 2 : ℚ) * X).natDegree = 1 := natDegree_C_mul_X (1 / 2 : ℚ) rat_half_ne_zero
  have h2 : ((X : ℚ[X]) ^ 2).natDegree = 2 := natDegree_X_pow 2
  have hlt : (C (1 / 2 : ℚ) * X).natDegree < ((X : ℚ[X]) ^ 2).natDegree := by
    rw [h1, h2]
    decide
  unfold chi2
  rw [natDegree_add_eq_left_of_natDegree_lt hlt, h2]
theorem chi3_natDegree : chi3.natDegree = 3 := by
  unfold chi3
  exact natDegree_X_pow_add_C
theorem F2_reduction_branch :
    0 < (F2.map (Int.castRingHom (ZMod 2))).natDegree ∧
      (F2.map (Int.castRingHom (ZMod 2))).natDegree < chi2.natDegree := by
  rw [F2_mod2_natDegree, chi2_natDegree]
  exact ⟨by decide, by decide⟩
theorem F3_reduction_branch :
    (F3.map (Int.castRingHom (ZMod 3))).natDegree = 0 ∧
      (F3.map (Int.castRingHom (ZMod 3))).natDegree < chi3.natDegree := by
  rw [F3_mod3_natDegree, chi3_natDegree]
  exact ⟨rfl, by decide⟩
end ResultantIntegralityReductionCases
