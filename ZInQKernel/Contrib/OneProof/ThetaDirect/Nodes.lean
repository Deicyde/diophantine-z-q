import ZInQKernel.Contrib.OneProof.ThetaDirect.Valence

/-! # theta-direct (helper): algebraic theta-constant ratios at the two nodes `√2 + i` and `τ₂₄`

* `nodeAlg_om24`: at `Ω₂₄ = Ω(τ₂₄)` (the CM point of discriminant `−24`) every `θ_m/θ_{(0,0)}` is an algebraic
  number. From cm24-value's explicit squares `θ_m(Ω₂₄)² = E·Q_m(U)` (TailZ18 `sqc0`…`sqc9`), Landen's
  duplication, Jacobi's identity and `mpoly(k) = 0` for the singular modulus `k = θ₁₀(i√6)²/θ₀₀(i√6)²`
  (`CM24.mpoly_theta`; the computations `hx`, `hy`, `hz` of `CM24.thetaValueAtOmega24_of_mpoly`, repeated).
* `nodeAlg_cm4`: at `Ω₀ = Ω(√2 + i)` (the CM point of discriminant `−4`) every `θ_m/θ_{(0,0)}` is an algebraic
  number. From period-glue's factorization `θ_m(Ω₀) = u·Θ(τ₁)·Θ(τ₂)` (TailJ `thetaConst_factor`), the
  translation `τ ↦ τ + 1`, Mathlib's inversion `τ ↦ −1/τ` (cm24-value's `sA`, `sB`, `sC`), `θ₀₁(i) = θ₁₀(i)` and
  Jacobi's identity `θ₀₀(i)⁴ = θ₀₁(i)⁴ + θ₁₀(i)⁴`. -/

set_option linter.all false

noncomputable section

namespace HDec.ThetaDirect

open Complex
open scoped Real

/-! ## Membership in the field of algebraic numbers -/

theorem ofNat_mem' (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : ℂ) ∈ (algebraicClosure ℚ ℂ) := by
  have := natCast_mem (algebraicClosure ℚ ℂ) n
  simpa using this

theorem ratCast_mem' (q : ℚ) : (q : ℂ) ∈ (algebraicClosure ℚ ℂ) := SubfieldClass.ratCast_mem (algebraicClosure ℚ ℂ) q

theorem mem_of_pow_mem {x : ℂ} {n : ℕ} (hn : n ≠ 0) (h : x ^ n ∈ (algebraicClosure ℚ ℂ)) : x ∈ (algebraicClosure ℚ ℂ) := by
  rw [mem_algebraicClosure_iff] at *
  exact IsAlgebraic.of_pow (Nat.pos_of_ne_zero hn) h

/-- Algebraic theta-constant ratios at `Ω`. -/
def NodeAlg (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∃ m0 : PkgI1.Char2, PkgI1.thetaConst m0 Ω ≠ 0 ∧
    ∀ m, PkgI1.thetaConst m Ω / PkgI1.thetaConst m0 Ω ∈ algebraicClosure ℚ ℂ

theorem nodeAlg_of_sq {Ω : Matrix (Fin 2) (Fin 2) ℂ} (K : ℂ)
    (h : ∀ m, ∃ a ∈ (algebraicClosure ℚ ℂ), PkgI1.thetaConst m Ω ^ 2 = K * a) (m0 : PkgI1.Char2)
    (h0 : PkgI1.thetaConst m0 Ω ≠ 0) : NodeAlg Ω := by
  refine ⟨m0, h0, fun m => ?_⟩
  obtain ⟨a, ha, hsq⟩ := h m
  obtain ⟨a0, ha0, hsq0⟩ := h m0
  have hK : K * a0 ≠ 0 := by rw [← hsq0]; exact pow_ne_zero _ h0
  refine mem_of_pow_mem (n := 2) (by norm_num) ?_
  rw [div_pow, hsq, hsq0, mul_div_mul_left _ _ (left_ne_zero_of_mul hK)]
  exact div_mem ha ha0

theorem nodeAlg_of_mul {Ω : Matrix (Fin 2) (Fin 2) ℂ} (X : ℂ)
    (h : ∀ m, ∃ a ∈ (algebraicClosure ℚ ℂ), PkgI1.thetaConst m Ω = a * X) (m0 : PkgI1.Char2)
    (h0 : PkgI1.thetaConst m0 Ω ≠ 0) : NodeAlg Ω := by
  refine ⟨m0, h0, fun m => ?_⟩
  obtain ⟨a, ha, he⟩ := h m
  obtain ⟨a0, ha0, he0⟩ := h m0
  have hX : a0 * X ≠ 0 := by rw [← he0]; exact h0
  rw [he, he0, mul_div_mul_right _ _ (right_ne_zero_of_mul hX)]
  exact div_mem ha ha0

/-- The odd theta constants vanish (TailA's `thetaConst_odd`, in pkg-I1's normalization). -/
theorem thetaConst_odd' (Ω : Matrix (Fin 2) (Fin 2) ℂ) {m : PkgI1.Char2} (hm : m ∉ PkgI1.evenChars) :
    PkgI1.thetaConst m Ω = 0 := by
  rw [← HDec.HSyn.G0Split.ThetaPt.thetaConst_eq_pkgI1]
  exact HDec.HSyn.G0Split.ThetaPt.thetaConst_odd _ m
    (HDec.HSyn.G0Split.ThetaPt.ThetaSplit.isOddChar_of_not_even hm)

/-- All even theta constants are nonzero where `∏θ² ≠ 0`. -/
theorem thetaConst_ne_of_prod {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hP : PkgI1.thetaProd2 Ω ≠ 0)
    {m : PkgI1.Char2} (hm : m ∈ PkgI1.evenChars) : PkgI1.thetaConst m Ω ≠ 0 := by
  have := (Finset.prod_ne_zero_iff.mp hP) m hm
  exact fun h0 => this (by rw [h0]; ring)

/-! ## The node `τ₂₄`: `Ω₂₄` -/

open CM24 in
open HDec.LeafQCheck.HM.QMSplit.Value24 in
theorem nodeAlg_om24 : NodeAlg Om24 := by
  obtain ⟨hA0, hm⟩ := CM24.mpoly_theta
  set A0 := th1 τ6 0 0
  set A1 := th1 τ6 0 (1 / 2)
  set A2 := th1 τ6 (1 / 2) 0
  set B0 := th1 τ3 0 0
  set B1 := th1 τ3 0 (1 / 2)
  set B2 := th1 τ3 (1 / 2) 0
  set k := A2 ^ 2 / A0 ^ 2 with hkdef
  have hk : A2 ^ 2 = k * A0 ^ 2 := (div_mul_cancel₀ _ (pow_ne_zero 2 hA0)).symm
  have rB0 : B0 ^ 2 = A0 ^ 2 + A2 ^ 2 := by have := dupA τ3_im; rw [h2τ3] at this; exact this
  have rB1 : B1 ^ 2 = A0 ^ 2 - A2 ^ 2 := by have := dupB τ3_im; rw [h2τ3] at this; exact this
  have rB2 : B2 ^ 2 = 2 * A0 * A2 := by have := dupC τ3_im; rw [h2τ3] at this; exact this
  have rJ : A0 ^ 4 = A1 ^ 4 + A2 ^ 4 := jacobi τ6_im
  have hζ := zeta_sq
  set ζ := cexp (π * I / 4)
  have hx : U 0 0 ^ 2 = A0 ^ 4 * (1 - k) := by
    rw [U00]; linear_combination A0 ^ 2 * rB1 - A0 ^ 2 * hk
  have hy : U (1 / 2) 0 ^ 2 = A0 ^ 4 * (-k * (1 + k)) := by
    rw [U10]; linear_combination (A2 ^ 2 * B0 ^ 2) * I_sq - A2 ^ 2 * rB0 - (A0 ^ 2 + A2 ^ 2 + k * A0 ^ 2) * hk
  have hz : (U 0 (1 / 2) ^ 2) ^ 2 = A0 ^ 8 * (-4 * k * (1 - k ^ 2)) := by
    rw [U01]
    linear_combination (ζ ^ 2 + I) * A1 ^ 4 * B2 ^ 4 * hζ + A1 ^ 4 * B2 ^ 4 * I_sq
      - A1 ^ 4 * (B2 ^ 2 + 2 * A0 * A2) * rB2 + 4 * A0 ^ 2 * A2 ^ 2 * rJ
      + (-4 * A0 ^ 6 + 4 * A0 ^ 2 * (A2 ^ 4 + k * A0 ^ 2 * A2 ^ 2 + k ^ 2 * A0 ^ 4)) * hk
  -- `k` is algebraic (a root of `mpoly`)
  have hkA : k ∈ (algebraicClosure ℚ ℂ) := by
    rw [mem_algebraicClosure_iff]
    refine ⟨Polynomial.X ^ 4 + Polynomial.C 12 * Polynomial.X ^ 3 + Polynomial.C 2 * Polynomial.X ^ 2 -
      Polynomial.C 12 * Polynomial.X + 1, ?_, ?_⟩
    · intro h0
      have := congrArg (fun p : Polynomial ℚ => p.eval 0) h0
      simp at this
    · have : CM24Alg.mpoly k = 0 := hm
      unfold CM24Alg.mpoly at this
      simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_one]
      have e12 : (algebraMap ℚ ℂ) 12 = 12 := by simp
      have e2 : (algebraMap ℚ ℂ) 2 = 2 := by simp
      rw [e12, e2]
      exact this
  have hA4 : A0 ^ 4 ≠ 0 := pow_ne_zero _ hA0
  set u0 := U 0 0 / A0 ^ 2
  set u1 := U (1 / 2) 0 / A0 ^ 2
  set u2 := U 0 (1 / 2) / A0 ^ 2
  have hu0 : u0 ∈ (algebraicClosure ℚ ℂ) := by
    refine mem_of_pow_mem (n := 2) (by norm_num) ?_
    have : u0 ^ 2 = 1 - k := by
      simp only [u0, div_pow, hx, ← pow_mul]; field_simp; ring
    rw [this]; repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem)
  have hu1 : u1 ∈ (algebraicClosure ℚ ℂ) := by
    refine mem_of_pow_mem (n := 2) (by norm_num) ?_
    have : u1 ^ 2 = -k * (1 + k) := by
      simp only [u1, div_pow, hy, ← pow_mul]; field_simp; ring
    rw [this]; repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem)
  have hu2 : u2 ∈ (algebraicClosure ℚ ℂ) := by
    refine mem_of_pow_mem (n := 4) (by norm_num) ?_
    have : u2 ^ 4 = -4 * k * (1 - k ^ 2) := by
      have e : u2 ^ 4 = (U 0 (1 / 2) ^ 2) ^ 2 / A0 ^ 8 := by simp only [u2]; field_simp
      rw [e, hz]; field_simp
    rw [this]; repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem)
  have eU0 : U 0 0 = u0 * A0 ^ 2 := by simp only [u0]; field_simp
  have eU1 : U (1 / 2) 0 = u1 * A0 ^ 2 := by simp only [u1]; field_simp
  have eU2 : U 0 (1 / 2) = u2 * A0 ^ 2 := by simp only [u2]; field_simp
  have hP : PkgI1.thetaProd2 Om24 ≠ 0 := by
    obtain ⟨hD, hv⟩ := thetaValueAtOmega24
    intro h0
    rw [PkgI1.jNum, h0] at hv
    norm_num at hv
  refine nodeAlg_of_sq (Ecal * A0 ^ 4) (fun m => ?_) ((0, 0) : PkgI1.Char2)
    (thetaConst_ne_of_prod hP HDec.HSyn.G0Split.ThetaPt.ThetaSplit.zero_mem_evenChars)
  by_cases hmE : m ∈ PkgI1.evenChars
  · rw [CM24.evenChars_eq] at hmE
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmE
    rcases hmE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨u0 ^ 2 + u1 ^ 2 + u2 ^ 2, by repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem), by rw [sqc0]; simp only [eU0, eU1, eU2]; ring⟩
    · exact ⟨u0 ^ 2 + u1 ^ 2 - u2 ^ 2, by repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem), by rw [sqc1]; simp only [eU0, eU1, eU2]; ring⟩
    · exact ⟨u0 ^ 2 - u1 ^ 2 + u2 ^ 2, by repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem), by rw [sqc2]; simp only [eU0, eU1, eU2]; ring⟩
    · exact ⟨u0 ^ 2 - u1 ^ 2 - u2 ^ 2, by repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem), by rw [sqc3]; simp only [eU0, eU1, eU2]; ring⟩
    · exact ⟨2 * u0 * u1, by repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem), by rw [sqc4]; simp only [eU0, eU1, eU2]; ring⟩
    · exact ⟨2 * u0 * u1, by repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem), by rw [sqc5]; simp only [eU0, eU1, eU2]; ring⟩
    · exact ⟨2 * u0 * u2, by repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem), by rw [sqc6]; simp only [eU0, eU1, eU2]; ring⟩
    · exact ⟨2 * u0 * u2, by repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem), by rw [sqc7]; simp only [eU0, eU1, eU2]; ring⟩
    · exact ⟨2 * u2 * u1, by repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem), by rw [sqc8]; simp only [eU0, eU1, eU2]; ring⟩
    · exact ⟨-(2 * u2 * u1), by repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem), by rw [sqc9]; simp only [eU0, eU1, eU2]; ring⟩
  · exact ⟨0, zero_mem _, by rw [thetaConst_odd' _ hmE]; ring⟩

/-- The node `τ₂₄` in the form used below. -/
theorem nodeAlg_tau24 :
    NodeAlg (PkgI1.Omega ((HDec.LeafQCheck.HM.QMSplit.Value24.tau24 : UpperHalfPlane) : ℂ)) := by
  have e : ((HDec.LeafQCheck.HM.QMSplit.Value24.tau24 : UpperHalfPlane) : ℂ) =
      Complex.I * (HDec.LeafQCheck.HM.QMSplit.Value24.s24 : ℂ) := rfl
  rw [e, HDec.LeafQCheck.HM.QMSplit.Value24.omega_tau24]
  exact nodeAlg_om24

/-! ## The node `√2 + i`: `Ω₀`, genus one at `i` -/

/-- period-glue's one-variable theta (characteristics `a/2`, `b/2`) is cm24-value's `th1`. -/
theorem pg_th1_eq (a b : ℕ) (τ : ℂ) :
    HDec.HSyn.G0Split.FibreQM.PeriodGlue.th1 a b τ = CM24.th1 τ ((a : ℝ) / 2) ((b : ℝ) / 2) := by
  unfold HDec.HSyn.G0Split.FibreQM.PeriodGlue.th1 CM24.th1
  refine tsum_congr fun n => ?_
  unfold HDec.HSyn.G0Split.FibreQM.PeriodGlue.thT CM24.term1
  congr 1; push_cast; ring

theorem exp_even_piI {n : ℤ} (hn : Even n) : cexp (π * I * n) = 1 := by
  obtain ⟨r, rfl⟩ := hn
  rw [show (π : ℂ) * I * ((r + r : ℤ) : ℂ) = (r : ℂ) * (2 * π * I) by push_cast; ring]
  exact exp_int_mul_two_pi_mul_I r

/-- Translation, characteristic `0`: `θ[0, d](τ + 1) = θ[0, d + 1/2](τ)`. -/
theorem th1_add_one_zero (τ : ℂ) (d : ℝ) : CM24.th1 (τ + 1) 0 d = CM24.th1 τ 0 (d + 1 / 2) := by
  unfold CM24.th1
  refine tsum_congr fun n => ?_
  unfold CM24.term1
  have h : cexp (π * I * ((n * n - n : ℤ) : ℂ)) = 1 := exp_even_piI (by
    rw [show n * n - n = n * (n - 1) by ring]; exact Int.even_mul_pred_self n)
  have e : π * I * (τ + 1) * ((((n : ℝ) + 0 : ℝ)) : ℂ) ^ 2 + 2 * π * I * ((((n : ℝ) + 0 : ℝ)) : ℂ) * (d : ℂ) =
      (π * I * τ * ((((n : ℝ) + 0 : ℝ)) : ℂ) ^ 2 + 2 * π * I * ((((n : ℝ) + 0 : ℝ)) : ℂ) * ((d + 1 / 2 : ℝ) : ℂ)) +
        π * I * ((n * n - n : ℤ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.exp_add, h, mul_one]

/-- Translation, characteristic `1/2`: `θ[1/2, d](τ + 1) = e^{πi/4} θ[1/2, d](τ)`. -/
theorem th1_add_one_half (τ : ℂ) (d : ℝ) :
    CM24.th1 (τ + 1) (1 / 2) d = cexp (π * I / 4) * CM24.th1 τ (1 / 2) d := by
  unfold CM24.th1
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  unfold CM24.term1
  have h : cexp (π * I * ((n * n + n : ℤ) : ℂ)) = 1 := exp_even_piI (by
    rw [show n * n + n = n * (n + 1) by ring]; exact Int.even_mul_succ_self n)
  have e : π * I * (τ + 1) * ((((n : ℝ) + 1 / 2 : ℝ)) : ℂ) ^ 2 +
        2 * π * I * ((((n : ℝ) + 1 / 2 : ℝ)) : ℂ) * (d : ℂ) =
      π * I / 4 + ((π * I * τ * ((((n : ℝ) + 1 / 2 : ℝ)) : ℂ) ^ 2 +
        2 * π * I * ((((n : ℝ) + 1 / 2 : ℝ)) : ℂ) * (d : ℂ)) + π * I * ((n * n + n : ℤ) : ℂ)) := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_add, h, mul_one]

theorem exp_pi4_mem : cexp (π * I / 4) ∈ (algebraicClosure ℚ ℂ) := by
  refine mem_of_pow_mem (n := 8) (by norm_num) ?_
  rw [← Complex.exp_nat_mul, show ((8 : ℕ) : ℂ) * (π * I / 4) = ((1 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
    exp_int_mul_two_pi_mul_I]
  exact one_mem _

theorem exp_neg_pi4_mem : cexp (-(π * I / 4)) ∈ (algebraicClosure ℚ ℂ) := by
  rw [Complex.exp_neg]; exact inv_mem exp_pi4_mem

/-- The values at `i`. -/
abbrev V00 : ℂ := CM24.th1 I 0 0
abbrev V01 : ℂ := CM24.th1 I 0 (1 / 2)
abbrev V10 : ℂ := CM24.th1 I (1 / 2) 0

theorem I_im_pos : 0 < I.im := by simp

theorem V00_ne : V00 ≠ 0 := by
  have h := CM24.th1_imag 1 0
  have hp := CM24.th1_imag_pos (t := 1) one_pos 0
  rw [show I * ((1 : ℝ) : ℂ) = I by simp] at h
  rw [V00, h]; exact_mod_cast hp.ne'

theorem V01_eq_V10 : V01 = V10 := by
  rw [V01, CM24.sB I_ne_zero]
  rw [show -I * I = 1 by rw [neg_mul, I_mul_I, neg_neg], Complex.one_cpow,
    show (-1 : ℂ) / I = I by rw [div_I]; simp]
  norm_num [V10]

theorem V01_pow4 : V01 ^ 4 * 2 = V00 ^ 4 := by
  have hJ : V00 ^ 4 = V01 ^ 4 + V10 ^ 4 := CM24.jacobi I_im_pos
  rw [← V01_eq_V10] at hJ
  linear_combination -hJ

theorem V01_ratio_mem : V01 / V00 ∈ (algebraicClosure ℚ ℂ) := by
  refine mem_of_pow_mem (n := 4) (by norm_num) ?_
  have : (V01 / V00) ^ 4 = 1 / 2 := by
    rw [div_pow, div_eq_iff (pow_ne_zero _ V00_ne)]; linear_combination (1 / 2 : ℂ) * V01_pow4
  rw [this]; repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem)

theorem V01_ne : V01 ≠ 0 := by
  intro h; have := V01_pow4; rw [h] at this; simp at this
  exact V00_ne (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0) |>.mp this.symm)

/-- `τ₁ = (−1+i)/2`, `−1/τ₁ = 1 + i`. -/
theorem neg_inv_τ1 : -1 / HDec.HSyn.G0Split.FibreQM.PeriodGlue.τ1 = I + 1 := by
  unfold HDec.HSyn.G0Split.FibreQM.PeriodGlue.τ1
  have h : (-1 + I) / 2 ≠ 0 := by
    intro h0; have := congrArg Complex.im h0; simp at this
  rw [div_eq_iff h]; ring_nf; rw [I_sq]; ring

theorem τ1_ne : HDec.HSyn.G0Split.FibreQM.PeriodGlue.τ1 ≠ 0 := by
  unfold HDec.HSyn.G0Split.FibreQM.PeriodGlue.τ1
  intro h0; have := congrArg Complex.im h0; simp at this

/-- The inversion factor at `τ₁`. -/
abbrev Kτ : ℂ := 1 / (-I * HDec.HSyn.G0Split.FibreQM.PeriodGlue.τ1) ^ (1 / 2 : ℂ)

theorem Kτ_ne : Kτ ≠ 0 := by
  apply one_div_ne_zero
  rw [Ne, Complex.cpow_eq_zero_iff]
  push_neg
  intro h; exfalso
  exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero) τ1_ne h

theorem pg_cases (τ : ℂ) :
    HDec.HSyn.G0Split.FibreQM.PeriodGlue.th1 0 0 τ = CM24.th1 τ 0 0 ∧
    HDec.HSyn.G0Split.FibreQM.PeriodGlue.th1 0 1 τ = CM24.th1 τ 0 (1 / 2) ∧
    HDec.HSyn.G0Split.FibreQM.PeriodGlue.th1 0 2 τ = CM24.th1 τ 0 1 ∧
    HDec.HSyn.G0Split.FibreQM.PeriodGlue.th1 1 0 τ = CM24.th1 τ (1 / 2) 0 ∧
    HDec.HSyn.G0Split.FibreQM.PeriodGlue.th1 1 1 τ = CM24.th1 τ (1 / 2) (1 / 2) ∧
    HDec.HSyn.G0Split.FibreQM.PeriodGlue.th1 1 2 τ = CM24.th1 τ (1 / 2) 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [pg_th1_eq] <;> congr 1 <;> norm_num

theorem th1_d1' (τ : ℂ) : CM24.th1 τ 0 1 = CM24.th1 τ 0 0 := by
  rw [CM24.th1_d1]; simp

theorem th1_d1'' (τ : ℂ) : CM24.th1 τ (1 / 2) 1 = -CM24.th1 τ (1 / 2) 0 := by
  rw [CM24.th1_d1, CM24.exp_half]; ring

/-- `θ_{(a,b)}(τ₁) ∈ (algebraicClosure ℚ ℂ)·Kτ·θ₀₀(i)`. -/
theorem th1_τ1_mem (a b : ℕ) (ha : a ≤ 1) (hb : b ≤ 2) :
    ∃ α ∈ (algebraicClosure ℚ ℂ), HDec.HSyn.G0Split.FibreQM.PeriodGlue.th1 a b HDec.HSyn.G0Split.FibreQM.PeriodGlue.τ1 =
      α * (Kτ * V00) := by
  have r00 : CM24.th1 HDec.HSyn.G0Split.FibreQM.PeriodGlue.τ1 0 0 = Kτ * V01 := by
    rw [CM24.sA, neg_inv_τ1, th1_add_one_zero]; norm_num
  have r01 : CM24.th1 HDec.HSyn.G0Split.FibreQM.PeriodGlue.τ1 0 (1 / 2) =
      Kτ * (cexp (π * I / 4) * V10) := by
    rw [CM24.sB τ1_ne, neg_inv_τ1, th1_add_one_half]
  have r10 : CM24.th1 HDec.HSyn.G0Split.FibreQM.PeriodGlue.τ1 (1 / 2) 0 = Kτ * V00 := by
    rw [CM24.sC τ1_ne, neg_inv_τ1, th1_add_one_zero, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, th1_d1']
  have c00 : ∃ α ∈ (algebraicClosure ℚ ℂ), CM24.th1 HDec.HSyn.G0Split.FibreQM.PeriodGlue.τ1 0 0 = α * (Kτ * V00) :=
    ⟨V01 / V00, V01_ratio_mem, by rw [r00]; field_simp [V00_ne]⟩
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := pg_cases HDec.HSyn.G0Split.FibreQM.PeriodGlue.τ1
  interval_cases a <;> interval_cases b
  · rw [p1]; exact c00
  · rw [p2]; exact ⟨cexp (π * I / 4) * (V01 / V00), mul_mem exp_pi4_mem V01_ratio_mem, by
      rw [r01, ← V01_eq_V10]; field_simp [V00_ne]⟩
  · rw [p3, th1_d1']; exact c00
  · rw [p4]; exact ⟨1, one_mem _, by rw [r10]; ring⟩
  · rw [p5, CM24.th1_odd]; exact ⟨0, zero_mem _, by ring⟩
  · rw [p6, th1_d1'', r10]; exact ⟨-1, neg_mem (one_mem _), by ring⟩

theorem τ2_add_one : HDec.HSyn.G0Split.FibreQM.PeriodGlue.τ2 + 1 = I := by
  unfold HDec.HSyn.G0Split.FibreQM.PeriodGlue.τ2; ring

/-- `θ_{(a,b)}(τ₂) ∈ (algebraicClosure ℚ ℂ)·θ₀₀(i)`. -/
theorem th1_τ2_mem (a b : ℕ) (ha : a ≤ 1) (hb : b ≤ 2) :
    ∃ β ∈ (algebraicClosure ℚ ℂ), HDec.HSyn.G0Split.FibreQM.PeriodGlue.th1 a b HDec.HSyn.G0Split.FibreQM.PeriodGlue.τ2 =
      β * V00 := by
  set t2 := HDec.HSyn.G0Split.FibreQM.PeriodGlue.τ2
  have r00 : CM24.th1 t2 0 0 = V01 := by
    have h := th1_add_one_zero t2 (-1 / 2)
    rw [τ2_add_one, show (-1 / 2 : ℝ) + 1 / 2 = 0 by norm_num] at h
    rw [← h, show (-1 / 2 : ℝ) = 1 / 2 + ((-1 : ℤ) : ℝ) by norm_num, CM24.th1_shift_d]; norm_num [V01]
  have r01 : CM24.th1 t2 0 (1 / 2) = V00 := by
    have h := th1_add_one_zero t2 0
    rw [τ2_add_one, zero_add] at h
    exact h.symm
  have r10 : CM24.th1 t2 (1 / 2) 0 = cexp (-(π * I / 4)) * V10 := by
    have h := th1_add_one_half t2 0
    rw [τ2_add_one] at h
    rw [show V10 = CM24.th1 I (1 / 2) 0 from rfl, h, ← mul_assoc, ← Complex.exp_add, neg_add_cancel,
      Complex.exp_zero, one_mul]
  have c00 : ∃ β ∈ (algebraicClosure ℚ ℂ), CM24.th1 t2 0 0 = β * V00 :=
    ⟨V01 / V00, V01_ratio_mem, by rw [r00]; field_simp [V00_ne]⟩
  have c10 : ∃ β ∈ (algebraicClosure ℚ ℂ), CM24.th1 t2 (1 / 2) 0 = β * V00 :=
    ⟨cexp (-(π * I / 4)) * (V01 / V00), mul_mem exp_neg_pi4_mem V01_ratio_mem, by
      rw [r10, ← V01_eq_V10]; field_simp [V00_ne]⟩
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := pg_cases t2
  interval_cases a <;> interval_cases b
  · rw [p1]; exact c00
  · rw [p2, r01]; exact ⟨1, one_mem _, by ring⟩
  · rw [p3, th1_d1']; exact c00
  · rw [p4]; exact c10
  · rw [p5, CM24.th1_odd]; exact ⟨0, zero_mem _, by ring⟩
  · rw [p6, th1_d1'']
    obtain ⟨β, hβ, e⟩ := c10
    exact ⟨-β, neg_mem hβ, by rw [e]; ring⟩

theorem fin2_le (x : Fin 2) : (x : ℕ) ≤ 1 := Nat.lt_succ_iff.mp x.isLt

theorem phase_mem (x y : ℕ) : cexp (-(π * I * (x : ℂ) * (y : ℂ) / 2)) ∈ (algebraicClosure ℚ ℂ) := by
  refine mem_of_pow_mem (n := 4) (by norm_num) ?_
  have : cexp (-(π * I * (x : ℂ) * (y : ℂ) / 2)) ^ 4 = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    exact ⟨-((x : ℤ) * y), by push_cast; ring⟩
  rw [this]; exact one_mem _

/-- **The node `√2 + i` (proved):** algebraic theta-constant ratios at `Ω₀ = Ω(√2 + i)`. -/
theorem nodeAlg_cm4 : NodeAlg (PkgI1.Omega ((√2 : ℂ) + I)) := by
  rw [HDec.HSyn.G0Split.FibreQM.PeriodGlue.omega_cm4]
  refine nodeAlg_of_mul (Kτ * V00 * V00) (fun m => ?_) ((0, 0) : PkgI1.Char2) ?_
  · rw [HDec.HSyn.G0Split.FibreQM.PeriodGlue.thetaConst_factor]
    obtain ⟨α, hα, eα⟩ := th1_τ1_mem (m.1 0 : ℕ) ((m.2 0 : ℕ) + (m.1 1 : ℕ)) (fin2_le _)
      (by have := fin2_le (m.2 0); have := fin2_le (m.1 1); omega)
    obtain ⟨β, hβ, eβ⟩ := th1_τ2_mem (m.1 1 : ℕ) ((m.2 1 : ℕ) + (m.1 0 : ℕ)) (fin2_le _)
      (by have := fin2_le (m.2 1); have := fin2_le (m.1 0); omega)
    refine ⟨cexp (-(π * I * ((m.1 0 : ℕ) : ℂ) * ((m.1 1 : ℕ) : ℂ) / 2)) * α * β,
      mul_mem (mul_mem (phase_mem _ _) hα) hβ, ?_⟩
    rw [eα, eβ]; ring
  · rw [HDec.HSyn.G0Split.FibreQM.PeriodGlue.thetaConst_factor]
    obtain ⟨p1, -, -, -, -, -⟩ := pg_cases HDec.HSyn.G0Split.FibreQM.PeriodGlue.τ1
    obtain ⟨q1, -, -, -, -, -⟩ := pg_cases HDec.HSyn.G0Split.FibreQM.PeriodGlue.τ2
    have e1 : CM24.th1 HDec.HSyn.G0Split.FibreQM.PeriodGlue.τ1 0 0 = Kτ * V01 := by
      rw [CM24.sA, neg_inv_τ1, th1_add_one_zero]; norm_num
    have e2 : CM24.th1 HDec.HSyn.G0Split.FibreQM.PeriodGlue.τ2 0 0 = V01 := by
      have h := th1_add_one_zero HDec.HSyn.G0Split.FibreQM.PeriodGlue.τ2 (-1 / 2)
      rw [τ2_add_one, show (-1 / 2 : ℝ) + 1 / 2 = 0 by norm_num] at h
      rw [← h, show (-1 / 2 : ℝ) = 1 / 2 + ((-1 : ℤ) : ℝ) by norm_num, CM24.th1_shift_d]; norm_num [V01]
    simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, Fin.val_zero, Nat.cast_zero, mul_zero,
      zero_div, neg_zero, Complex.exp_zero, one_mul, add_zero]
    rw [p1, q1, e1, e2]
    exact mul_ne_zero (mul_ne_zero Kτ_ne V01_ne) V01_ne

end HDec.ThetaDirect
