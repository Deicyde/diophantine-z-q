import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.CoprimeProductTraceInvariance

/-!
# Actual torsion-point splitting and its pairing phase

A Bézout decomposition splits every actual pℓ-torsion point as an ℓ-torsion
point plus a p-torsion point. The br-as exponential pairing splits with the
p and ℓ factors and an integer cross term of phase one.
-/

noncomputable section
set_option autoImplicit false
open Complex UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace

/-- Actual integer Bézout coefficients for the coprime level pair. -/
theorem level_bezout (p N : ℕ) (hcop : Nat.Coprime p N) :
    ∃ u v : ℤ, (p : ℤ) * u + (N : ℤ) * v = 1 := by
  refine ⟨Nat.gcdA p N, Nat.gcdB p N, ?_⟩
  have h := Nat.gcd_eq_gcd_ab p N
  rw [hcop.gcd_eq_one] at h
  exact h.symm

/-- Every actual torsion point has an explicit coprime direct-sum expression. -/
theorem actual_torsion_split (p N : ℕ) (hp : 0 < p) (hN : 0 < N)
    (hcop : Nat.Coprime p N) (r s : ℤ) :
    ∃ a b t u : ℤ,
      r = (p : ℤ) * a + (N : ℤ) * t ∧ s = (p : ℤ) * b + (N : ℤ) * u ∧
      ∀ τ : ℍ, CompletedTheta.torsionPoint (p * N) r s τ =
        CompletedTheta.torsionPoint N a b τ + CompletedTheta.torsionPoint p t u τ := by
  obtain ⟨x, y, hxy⟩ := level_bezout p N hcop
  have hr : r = (p : ℤ) * (x * r) + (N : ℤ) * (y * r) := by
    linear_combination -r * hxy
  have hs : s = (p : ℤ) * (x * s) + (N : ℤ) * (y * s) := by
    linear_combination -s * hxy
  refine ⟨x * r, x * s, y * r, y * s, hr, hs, ?_⟩
  intro τ
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold CompletedTheta.torsionPoint
  nth_rewrite 1 [hr]
  nth_rewrite 1 [hs]
  push_cast
  field_simp

/-- The explicit pN integer label of A+T. -/
def splitLabel (p N : ℕ) (A T : ℤ × ℤ) : ℤ × ℤ :=
  ((p : ℤ) * A.1 + (N : ℤ) * T.1, (p : ℤ) * A.2 + (N : ℤ) * T.2)

/-- The exact phase split in the actual torsion pairing. -/
theorem character_split (p N : ℕ) [NeZero p] [NeZero N] [NeZero (p * N)]
    (A T B U : ℤ × ℤ) :
    TorsionFourierComparison.character (p * N) (splitLabel p N A T).1 (splitLabel p N A T).2
        (splitLabel p N B U).1 (splitLabel p N B U).2 =
      TorsionFourierComparison.character N ((p : ℤ) * A.1) ((p : ℤ) * A.2) B.1 B.2 *
        TorsionFourierComparison.character p ((N : ℤ) * T.1) ((N : ℤ) * T.2) U.1 U.2 := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  unfold TorsionFourierComparison.character splitLabel
  let c : ℤ := A.2 * U.1 - A.1 * U.2 + T.2 * B.1 - T.1 * B.2
  have he : 2 * (Real.pi : ℂ) * Complex.I *
      (((p : ℂ) * A.2 + N * T.2) * ((p : ℂ) * B.1 + N * U.1) -
       ((p : ℂ) * A.1 + N * T.1) * ((p : ℂ) * B.2 + N * U.2)) / ((p : ℂ) * N) =
      2 * (Real.pi : ℂ) * Complex.I * (((p : ℂ) * A.2) * B.1 - ((p : ℂ) * A.1) * B.2) / N +
        2 * (Real.pi : ℂ) * Complex.I * (((N : ℂ) * T.2) * U.1 - ((N : ℂ) * T.1) * U.2) / p +
        (c : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    dsimp [c]
    push_cast
    field_simp
    ring
  push_cast
  rw [he, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The negative determinant phase is literally the actual exponential,
not a sign convention adopted without recomputation. -/
theorem determinant_phase_exp (p N : ℕ) [NeZero p] (d s : ZMod p) :
    phase p (-(N : ZMod p) * d * s) =
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (N : ℂ) * (d.val : ℂ) * (s.val : ℂ) / (p : ℂ)) := by
  have h := phase_eq_exp p (-((N : ℤ) * (d.val : ℤ) * (s.val : ℤ)))
  simp only [Int.cast_neg, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] at h
  convert h using 1 <;> congr 1 <;> ring

end ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace
