/-
Plan step 3.2: the signature of `ℚ(√d)`.
-/
import ZInQKernel.Progressions.QuadField.Basic

namespace ZInQ.Progressions

open NumberField NumberField.InfinitePlace QuadraticAlgebra ComplexConjugate

variable {d : ℤ}

/-- A ring homomorphism out of `ℚ(√d)` into a field of characteristic zero is determined by
the image of `ω`. -/
theorem Qsqrt.ringHom_apply {F : Type*} [DivisionRing F] [CharZero F]
    [Fact (¬ IsSquare (d : ℚ))] (φ : Qsqrt d →+* F) (z : Qsqrt d) :
    φ z = (z.re : F) + (z.im : F) * φ ω := by
  have hq : ∀ q : ℚ, φ (algebraMap ℚ (Qsqrt d) q) = q := fun q =>
    eq_ratCast (φ.comp (algebraMap ℚ (Qsqrt d))) q
  conv_lhs => rw [← re_smul_add_im_smul z]
  rw [Algebra.smul_def, Algebra.smul_def, map_add, map_mul, map_mul, hq, hq, map_one, mul_one]

/-- The image of `ω` squares to `d`. -/
theorem Qsqrt.ringHom_omega_sq {F : Type*} [DivisionRing F] [CharZero F]
    [Fact (¬ IsSquare (d : ℚ))] (φ : Qsqrt d →+* F) : φ ω ^ 2 = (d : F) := by
  have h : (ω : Qsqrt d) ^ 2 = algebraMap ℚ (Qsqrt d) (d : ℚ) := by
    rw [sq, omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero]
  rw [← map_pow, h]
  simp

variable [Fact (¬ IsSquare (d : ℚ))]

/-- For `d > 0`, every complex embedding of `ℚ(√d)` is real. -/
theorem Qsqrt.isTotallyReal (hd : 0 < d) : IsTotallyReal (Qsqrt d) := by
  refine ⟨fun w => isReal_iff.mpr ?_⟩
  set φ := w.embedding
  have hω : (φ ω).im = 0 := by
    have h := Qsqrt.ringHom_omega_sq φ
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im] at hre him
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    by_contra hne
    have : (φ ω).re = 0 := by
      have : (φ ω).im * (φ ω).re = 0 := by linarith
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hne
      · exact h0
    rw [this] at hre
    nlinarith [sq_nonneg (φ ω).im]
  have hc : conj (φ ω) = φ ω := Complex.conj_eq_iff_im.mpr hω
  rw [ComplexEmbedding.isReal_iff]
  ext1 z
  rw [ComplexEmbedding.conjugate_coe_eq, Qsqrt.ringHom_apply φ z]
  simp [hc]

/-- For `d < 0`, no complex embedding of `ℚ(√d)` is real. -/
theorem Qsqrt.isTotallyComplex (hd : d < 0) : IsTotallyComplex (Qsqrt d) := by
  refine ⟨fun w => isComplex_iff.mpr fun hw => ?_⟩
  set φ := w.embedding
  have h := Qsqrt.ringHom_omega_sq φ
  have hc : conj (φ ω) = φ ω := by
    rw [← ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.isReal_iff.mp hw]
  have him : (φ ω).im = 0 := by
    have := congrArg Complex.im hc
    simp at this
    linarith
  have hre := congrArg Complex.re h
  simp only [sq, Complex.mul_re, Complex.intCast_re, him, mul_zero, sub_zero] at hre
  have hd' : (d : ℝ) < 0 := by exact_mod_cast hd
  nlinarith [mul_self_nonneg (φ ω).re]

/-- Signature of a real quadratic field: two real places, no complex place. -/
theorem Qsqrt.nrRealPlaces_of_pos (hd : 0 < d) : nrRealPlaces (Qsqrt d) = 2 := by
  have := Qsqrt.isTotallyReal hd
  have h0 : nrComplexPlaces (Qsqrt d) = 0 := nrComplexPlaces_eq_zero_iff.mpr this
  have h := card_add_two_mul_card_eq_rank (Qsqrt d)
  rw [h0, Qsqrt.finrank] at h
  omega

theorem Qsqrt.nrComplexPlaces_of_pos (hd : 0 < d) : nrComplexPlaces (Qsqrt d) = 0 :=
  nrComplexPlaces_eq_zero_iff.mpr (Qsqrt.isTotallyReal hd)

/-- Signature of an imaginary quadratic field: no real place, one complex place. -/
theorem Qsqrt.nrRealPlaces_of_neg (hd : d < 0) : nrRealPlaces (Qsqrt d) = 0 :=
  nrRealPlaces_eq_zero_iff.mpr (Qsqrt.isTotallyComplex hd)

theorem Qsqrt.nrComplexPlaces_of_neg (hd : d < 0) : nrComplexPlaces (Qsqrt d) = 1 := by
  have h0 := Qsqrt.nrRealPlaces_of_neg hd
  have h := card_add_two_mul_card_eq_rank (Qsqrt d)
  rw [h0, Qsqrt.finrank] at h
  omega

end ZInQ.Progressions
