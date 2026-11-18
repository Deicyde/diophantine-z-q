import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TateOdd
import ZInQKernel.Contrib.CloudB3RC53.OpenImage.Basic

/-! The actual complex conjugation used at tex 8340–8356. -/

noncomputable section

open TauCeti ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.GlueSweep.Tate ZInQ.Manuscript.RC.TateWiring
  ZInQ.Contrib.CloudB3RC53.OpenImage

namespace ZInQ.Manuscript.RC.Stages

/-- The chosen actual complex conjugation squares to one in the absolute Galois group. -/
theorem complexConj_sq : complexConj * complexConj = 1 := by
  ext x
  apply iota.injective
  change iota (complexConj (complexConj x)) = iota x
  rw [iota_complexConj, iota_complexConj]
  exact star_star _

/-- Complex conjugation is inversion on the roots of unity, including at 2-power level. -/
theorem complexConj_rootOfUnity {n : ℕ} (hn : n ≠ 0) (x : Qbar) (hx : x ^ n = 1) :
    complexConj x = x ^ (n - 1) := by
  have hnx : ‖iota x‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, hx, map_one, norm_one]
  have hnorm : ‖iota x‖ = 1 := by
    rcases lt_trichotomy ‖iota x‖ 1 with hl | he | hg
    · have ht : ‖iota x‖ ^ n < (1 : ℝ) ^ n := by
        gcongr
      rw [hnx, one_pow] at ht
      exact (lt_irrefl _ ht).elim
    · exact he
    · have ht : (1 : ℝ) ^ n < ‖iota x‖ ^ n := by
        gcongr
      rw [hnx, one_pow] at ht
      exact (lt_irrefl _ ht).elim
  apply iota.injective
  change iota (complexConj x) = iota (x ^ (n - 1))
  rw [iota_complexConj, map_pow]
  have hi : (iota x)⁻¹ = starRingEnd ℂ (iota x) := Complex.inv_eq_conj hnorm
  rw [← hi]
  have hpow : iota x ^ (n - 1) * iota x = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn), ← map_pow, hx, map_one]
  calc
    (iota x)⁻¹ = ((iota x) ^ (n - 1) * iota x) * (iota x)⁻¹ := by rw [hpow, one_mul]
    _ = (iota x) ^ (n - 1) := by
      rw [mul_assoc, mul_inv_cancel₀ (right_ne_zero_of_mul_eq_one hpow), mul_one]

/-- The 2-adic determinant of actual complex conjugation is minus one. -/
theorem det_complexConj (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (tateMatrix E complexConj).det = -1 := by
  rw [det_tateMatrix]
  apply PadicInt.ext_of_toZModPow.mp
  intro M
  rw [toZModPow_det_eq_of_frob E complexConj (complexConj_rootOfUnity (pow_ne_zero M (by decide))),
    map_neg, map_one, Nat.cast_sub (Nat.one_le_pow M 2 (by decide)), Nat.cast_one,
    ZMod.natCast_self, zero_sub]

/-- Actual conjugation fixes a square root of a positive integer. -/
theorem complexConj_pos_sqrt {D : ℤ} (hD : 0 < D) {x : Qbar} (hx : x ^ 2 = (D : Qbar)) :
    complexConj x = x := by
  have hz : (iota x) ^ 2 = (D : ℂ) := by rw [← map_pow, hx, map_intCast]
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im] at hre him
  have hne : (iota x).re ≠ 0 := by
    intro h
    have hn : (0 : ℝ) < D := by exact_mod_cast hD
    rw [h, zero_mul, zero_sub] at hre
    nlinarith [sq_nonneg (iota x).im]
  have hi : (iota x).im = 0 := by
    by_contra h
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hne) h) (by linarith)
  apply iota.injective
  change iota (complexConj x) = iota x
  rw [iota_complexConj]
  apply Complex.ext <;> simp [hi]

/-- Actual conjugation negates a square root of a negative integer. -/
theorem complexConj_neg_sqrt {D : ℤ} (hD : D < 0) {x : Qbar} (hx : x ^ 2 = (D : Qbar)) :
    complexConj x = -x := by
  have hfixed : complexConj x ≠ x := by
    exact complexConj_not_mem (k := (D : ℚ)) (by exact_mod_cast hD) (by simpa using hx)
  have heq : (complexConj x) ^ 2 = x ^ 2 := by rw [← map_pow, hx, map_intCast]
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp heq).resolve_left hfixed

/-- The selected translation does not change the prescribed signs on the
two quadratic subfields of the fixed auxiliary field. -/
theorem detector_sqrt_signs (F : IntermediateField ℚ Qbar) {h : GalQ}
    (hh : h ∈ F.fixingSubgroup) {D k : ℤ} (hD : 0 < D) (hk : k < 0)
    {x y : Qbar} (hxf : x ∈ F) (hyf : y ∈ F)
    (hx : x ^ 2 = (D : Qbar)) (hy : y ^ 2 = (k : Qbar)) :
    (h * complexConj) x = x ∧ (h * complexConj) y = -y := by
  change h (complexConj x) = x ∧ h (complexConj y) = -y
  rw [complexConj_pos_sqrt hD hx, complexConj_neg_sqrt hk hy, map_neg]
  exact ⟨hh ⟨x, hxf⟩, congrArg Neg.neg (hh ⟨y, hyf⟩)⟩

#print axioms complexConj_sq
#print axioms complexConj_rootOfUnity
#print axioms det_complexConj
#print axioms complexConj_pos_sqrt
#print axioms complexConj_neg_sqrt
#print axioms detector_sqrt_signs

end ZInQ.Manuscript.RC.Stages
