import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinCompleteFibers
import Mathlib.Algebra.Field.ZMod

/-!
# Actual principal-congruence moves in a prime torsion fibre

When p divides N, a row nonzero modulo p can be moved by an actual integral
Gamma(N) matrix to every residue in its complete N-fibre modulo pN. The move
is constructed through a trace-zero infinitesimal matrix and a proved integral
special-linear lift. No orbit-size or trace-preservation conclusion is assumed.
-/

noncomputable section
set_option autoImplicit false
open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups Matrix

namespace ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLowerClosure

/-- An explicit trace-zero two-by-two coefficient solves every primitive row target. -/
theorem exists_trace_zero_coefficients (p : ℕ) [Fact p.Prime] (a b r s : ℤ)
    (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0) :
    ∃ x y z : ℤ, (p : ℤ) ∣ a * x + b * z - r ∧ (p : ℤ) ∣ a * y - b * x - s := by
  rcases hab with ha | hb
  · let X : ZMod p := (r : ZMod p) / a
    let Y : ZMod p := ((s : ZMod p) + b * X) / a
    refine ⟨ZMod.cast X, ZMod.cast Y, 0, ?_, ?_⟩
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, ZMod.intCast_zmod_cast,
        Int.cast_zero, mul_zero, add_zero]
      dsimp [X]
      field_simp
      ring
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simp only [Int.cast_sub, Int.cast_mul, ZMod.intCast_zmod_cast]
      dsimp [X, Y]
      field_simp
      ring
  · let X : ZMod p := -(s : ZMod p) / b
    let Z : ZMod p := ((r : ZMod p) - a * X) / b
    refine ⟨ZMod.cast X, 0, ZMod.cast Z, ?_, ?_⟩
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, ZMod.intCast_zmod_cast]
      dsimp [X, Z]
      field_simp
      ring
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_neg, ZMod.intCast_zmod_cast,
        Int.cast_zero, mul_zero, zero_sub]
      dsimp [X]
      field_simp
      ring

/-- A trace-zero first-order matrix really lifts to an integral principal group. -/
theorem exists_Gamma_lift_trace_zero (p N : ℕ) (hpN : p ∣ N) (x y z : ℤ) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma N ∧
      ∀ i j, (γ i j : ZMod (p * N)) =
        (((!![1 + (N : ℤ) * x, (N : ℤ) * y;
              (N : ℤ) * z, 1 - (N : ℤ) * x] : Matrix (Fin 2) (Fin 2) ℤ) i j) : ZMod (p * N)) := by
  let U : Matrix (Fin 2) (Fin 2) ℤ := !![1 + (N : ℤ) * x, (N : ℤ) * y;
    (N : ℤ) * z, 1 - (N : ℤ) * x]
  have hN2 : (N : ZMod (p * N)) ^ 2 = 0 := by
    have hd : ((p * N : ℕ) : ℤ) ∣ (N : ℤ) ^ 2 := by
      exact_mod_cast (show p * N ∣ N ^ 2 from by
        simpa only [pow_two] using Nat.mul_dvd_mul_right hpN N)
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd ((N : ℤ) ^ 2) (p * N)).mpr hd
    simpa only [Int.cast_pow, Int.cast_natCast] using hh
  have hdet : (U.map (Int.castRingHom (ZMod (p * N)))).det = 1 := by
    have hf : (U.map (Int.castRingHom (ZMod (p * N)))).det =
        1 - (N : ZMod (p * N)) ^ 2 * ((x : ZMod (p * N)) ^ 2 + y * z) := by
      simp [U, Matrix.det_fin_two]
      ring
    rw [hf, hN2, zero_mul, sub_zero]
  obtain ⟨γ, hγ⟩ := Matrix.SpecialLinearGroup.map_intCast_zmod_surjective
    (d := p * N) ⟨U.map (Int.castRingHom (ZMod (p * N))), hdet⟩
  have he (i j : Fin 2) : (γ i j : ZMod (p * N)) = (U i j : ZMod (p * N)) := by
    have h := congrArg (fun g : SL(2, ZMod (p * N)) => g i j) hγ
    simpa only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, Int.coe_castRingHom] using h
  have hn (i j : Fin 2) : (γ i j : ZMod N) = (U i j : ZMod N) := by
    have h := congrArg (ZMod.castHom (dvd_mul_left N p) (ZMod N)) (he i j)
    simpa only [map_intCast] using h
  refine ⟨γ, ?_, he⟩
  rw [Gamma_mem]
  simp [hn, U]

/-- Every residue in the full fibre is reached by an actual principal-group
matrix when the upper row is primitive modulo the repeated prime. -/
theorem exists_Gamma_prime_fiber_move (p N : ℕ) [Fact p.Prime] (hpN : p ∣ N)
    (a b r s : ℤ) (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma N ∧
      (((![a,b] ᵥ* γ.1) 0 : ℤ) : ZMod (p * N)) = ((a + (N : ℤ) * r : ℤ) : ZMod (p * N)) ∧
      (((![a,b] ᵥ* γ.1) 1 : ℤ) : ZMod (p * N)) = ((b + (N : ℤ) * s : ℤ) : ZMod (p * N)) := by
  obtain ⟨x, y, z, hr, hs⟩ := exists_trace_zero_coefficients p a b r s hab
  obtain ⟨γ, hγ, he⟩ := exists_Gamma_lift_trace_zero p N hpN x y z
  have hd0 : ((p * N : ℕ) : ℤ) ∣ (N : ℤ) * (a * x + b * z - r) := by
    simpa only [Nat.cast_mul, mul_comm] using mul_dvd_mul_right hr (N : ℤ)
  have hd1 : ((p * N : ℕ) : ℤ) ∣ (N : ℤ) * (a * y - b * x - s) := by
    simpa only [Nat.cast_mul, mul_comm] using mul_dvd_mul_right hs (N : ℤ)
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p * N)).mpr hd0
  have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p * N)).mpr hd1
  push_cast at h0 h1
  refine ⟨γ, hγ, ?_, ?_⟩
  · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, he]
    linear_combination h0
  · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, he]
    linear_combination h1

end ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLowerClosure
