import ZInQKernel.Multiplication.FormalLog.ChainRule
import ZInQKernel.Multiplication.Local.FormalGroupLaw

/-!
# The relations between the pieces of the formal group law

In `R⟦T₁, T₂⟧` (`R` any commutative ring, `A ∈ R`) put `ω₁ = ω(T₁)` (`omegaFst`),
`ω₂ = ω(T₂)` (`omegaSnd`), `λ = chordSlope A`, `ν = ω₁ - λT₁` and `I = (1 + Aλ²)⁻¹`. Then

* `ωᵢ = Tᵢ³ + A Tᵢ ωᵢ²` (`omegaFst_eq`, `omegaSnd_eq`);
* `λ (T₂ - T₁) = ω₂ - ω₁` (`chordSlope_mul_sub`): `λ` is the slope of the chord;
* `I (1 + Aλ²) = 1` (`chordInv_mul`), and `formalAdd A = T₁ + T₂ + 2AλνI` (`formalAdd_eq`);
* `ω' (1 - 2ATω) = 3T² + Aω²` (`derivative_omegaSeries_mul`), the derivative of the equation
  of `ω`.
-/

namespace ZInQ.Mult

open MvPowerSeries

variable {R : Type*} [CommRing R]

/-- `ω(T₂)` as a power series in two variables. -/
noncomputable def omegaSnd (A : R) : MvPowerSeries (Fin 2) R :=
  PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) (omegaSeries A)

/-- `(1 + Aλ²)⁻¹`, the last factor of `formalAdd A`. -/
noncomputable def chordInv (A : R) : MvPowerSeries (Fin 2) R :=
  MvPowerSeries.invOfUnit (1 + MvPowerSeries.C A * chordSlope A ^ 2) 1

theorem coeff_chordSlope (A : R) (n : Fin 2 →₀ ℕ) :
    coeff n (chordSlope A) = omegaCoeff A (n 0 + n 1 + 1) := rfl

theorem coeff_omegaFst (A : R) (n : Fin 2 →₀ ℕ) :
    coeff n (omegaFst A) = if n 1 = 0 then omegaCoeff A (n 0) else 0 := rfl

theorem constantCoeff_chordSlope (A : R) : constantCoeff (chordSlope A) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_chordSlope]
  simpa using omegaCoeff_one A

theorem finsupp_fin_two_eq_single_zero {n : Fin 2 →₀ ℕ} :
    n = Finsupp.single 0 (n 0) ↔ n 1 = 0 := by
  refine ⟨fun h => by rw [h]; simp, fun h => ?_⟩
  ext i; fin_cases i <;> simp [h]

theorem finsupp_fin_two_eq_single_one {n : Fin 2 →₀ ℕ} :
    n = Finsupp.single 1 (n 1) ↔ n 0 = 0 := by
  refine ⟨fun h => by rw [h]; simp, fun h => ?_⟩
  ext i; fin_cases i <;> simp [h]

theorem omegaFst_eq_subst (A : R) :
    omegaFst A = PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) (omegaSeries A) := by
  ext n
  rw [coeff_omegaFst, PowerSeries.coeff_subst_single, coeff_omegaSeries]
  simp only [finsupp_fin_two_eq_single_zero]

theorem coeff_omegaSnd (A : R) (n : Fin 2 →₀ ℕ) :
    coeff n (omegaSnd A) = if n 0 = 0 then omegaCoeff A (n 1) else 0 := by
  rw [omegaSnd, PowerSeries.coeff_subst_single, coeff_omegaSeries]
  simp only [finsupp_fin_two_eq_single_one]

/-- `f(a)` for the equation `ω = T³ + A T ω²`. -/
theorem subst_omegaSeries_eq {σ : Type*} {a : MvPowerSeries σ R} (ha : constantCoeff a = 0)
    (A : R) : PowerSeries.subst a (omegaSeries A) =
      a ^ 3 + MvPowerSeries.C A * a * PowerSeries.subst a (omegaSeries A) ^ 2 := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
  conv_lhs => rw [omegaSeries_eq A]
  rw [PowerSeries.subst_add hs, PowerSeries.subst_mul hs, PowerSeries.subst_mul hs,
    PowerSeries.subst_pow hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs,
    PowerSeries.subst_C]

theorem omegaFst_eq (A : R) :
    omegaFst A = MvPowerSeries.X 0 ^ 3 + MvPowerSeries.C A * MvPowerSeries.X 0 * omegaFst A ^ 2 := by
  rw [omegaFst_eq_subst]; exact subst_omegaSeries_eq (constantCoeff_X 0) A

theorem omegaSnd_eq (A : R) :
    omegaSnd A = MvPowerSeries.X 1 ^ 3 + MvPowerSeries.C A * MvPowerSeries.X 1 * omegaSnd A ^ 2 :=
  subst_omegaSeries_eq (constantCoeff_X 1) A

theorem coeff_mul_X_fin_two (f : MvPowerSeries (Fin 2) R) (i : Fin 2) (n : Fin 2 →₀ ℕ) :
    coeff n (f * MvPowerSeries.X i) =
      if 1 ≤ n i then coeff (n - Finsupp.single i 1) f else 0 := by
  classical
  rw [X_def, coeff_mul_monomial, mul_one]
  congr 1
  apply propext
  constructor
  · intro h; simpa using h i
  · intro h j
    by_cases hj : j = i
    · subst hj; simpa using h
    · simp [Finsupp.single_eq_of_ne hj]

/-- **`λ` is the slope of the chord**: `λ (T₂ - T₁) = ω₂ - ω₁`. -/
theorem chordSlope_mul_sub (A : R) :
    chordSlope A * (MvPowerSeries.X 1 - MvPowerSeries.X 0) = omegaSnd A - omegaFst A := by
  ext n
  rw [mul_sub, map_sub, map_sub, coeff_omegaSnd, coeff_omegaFst, coeff_mul_X_fin_two,
    coeff_mul_X_fin_two, coeff_chordSlope, coeff_chordSlope]
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
  rcases Nat.eq_zero_or_pos (n 0) with h0 | h0 <;> rcases Nat.eq_zero_or_pos (n 1) with h1 | h1
  · simp [h0, h1]
  · simp only [h0, Fin.isValue, zero_ne_one, ite_false, Nat.sub_zero, ite_true, show 1 ≤ n 1 by omega,
      show ¬ (1 ≤ (0 : ℕ)) by omega, ite_false, show n 1 ≠ 0 by omega, sub_zero]
    congr 1; omega
  · simp only [h1, Fin.isValue, one_ne_zero, ite_false, Nat.sub_zero, ite_true, show 1 ≤ n 0 by omega,
      show ¬ (1 ≤ (0 : ℕ)) by omega, ite_false, show n 0 ≠ 0 by omega, zero_sub]
    congr 2; omega
  · simp only [Fin.isValue, ite_true, show 1 ≤ n 0 by omega, show 1 ≤ n 1 by omega,
      show n 0 ≠ 0 by omega, show n 1 ≠ 0 by omega, ite_false, sub_zero]
    simp only [zero_ne_one, one_ne_zero, ite_false, Nat.sub_zero]
    rw [show n 0 + (n 1 - 1) + 1 = n 0 - 1 + n 1 + 1 by omega, sub_self]

theorem constantCoeff_chordDen (A : R) :
    constantCoeff (1 + MvPowerSeries.C A * chordSlope A ^ 2) = ((1 : Rˣ) : R) := by
  simp [constantCoeff_chordSlope]

theorem chordInv_mul (A : R) :
    chordInv A * (1 + MvPowerSeries.C A * chordSlope A ^ 2) = 1 :=
  invOfUnit_mul _ _ (constantCoeff_chordDen A)

theorem formalAdd_def (A : R) :
    formalAdd A = MvPowerSeries.X 0 + MvPowerSeries.X 1 +
      MvPowerSeries.C (2 * A) * chordSlope A *
        (omegaFst A - chordSlope A * MvPowerSeries.X 0) * chordInv A := rfl

theorem formalAdd_eq (A : R) :
    formalAdd A = MvPowerSeries.X 0 + MvPowerSeries.X 1 +
      2 * MvPowerSeries.C A * chordSlope A *
        (omegaFst A - chordSlope A * MvPowerSeries.X 0) * chordInv A := by
  rw [formalAdd, chordInv, map_mul, map_ofNat]

theorem constantCoeff_formalAdd (A : R) : constantCoeff (formalAdd A) = 0 := by
  rw [formalAdd_eq]
  simp [constantCoeff_chordSlope]

theorem constantCoeff_omegaFst (A : R) : constantCoeff (omegaFst A) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_omegaFst]
  simpa using omegaCoeff_zero A

theorem constantCoeff_omegaSnd (A : R) : constantCoeff (omegaSnd A) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_omegaSnd]
  simpa using omegaCoeff_zero A

/-- The derivative of `ω = T³ + A T ω²`: `ω' (1 - 2ATω) = 3T² + Aω²`. -/
theorem derivative_omegaSeries_mul (A : R) :
    PowerSeries.derivative (R := R) (omegaSeries A) *
        (1 - 2 * PowerSeries.C A * PowerSeries.X * omegaSeries A) =
      3 * PowerSeries.X ^ 2 + PowerSeries.C A * omegaSeries A ^ 2 := by
  have h := congrArg (PowerSeries.derivative (R := R)) (omegaSeries_eq A)
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, PowerSeries.derivative_C,
    PowerSeries.derivative_X, smul_eq_mul, nsmul_eq_mul] at h
  push_cast at h
  linear_combination h


/-- `ω'(a) (1 - 2A a ω(a)) = 3a² + A ω(a)²` for `a` with constant coefficient `0`. -/
theorem subst_derivative_omegaSeries_mul {σ : Type*} {a : MvPowerSeries σ R}
    (ha : constantCoeff a = 0) (A : R) :
    PowerSeries.subst a (PowerSeries.derivative (R := R) (omegaSeries A)) *
        (1 - 2 * MvPowerSeries.C A * a * PowerSeries.subst a (omegaSeries A)) =
      3 * a ^ 2 + MvPowerSeries.C A * PowerSeries.subst a (omegaSeries A) ^ 2 := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have h := congrArg (PowerSeries.substAlgHom (R := R) hs) (derivative_omegaSeries_mul A)
  simp only [map_mul, map_sub, map_add, map_one, map_pow, map_ofNat,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs, PowerSeries.subst_C] at h
  exact h

/-- `∂ᵢ ω(Tⱼ) = δᵢⱼ ω'(Tⱼ)`. -/
theorem pderiv_subst_X (i j : Fin 2) (f : PowerSeries R) :
    pderiv i (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) R) f) =
      if j = i then PowerSeries.subst (MvPowerSeries.X j) (PowerSeries.derivative (R := R) f)
      else 0 := by
  rw [pderiv_subst i (constantCoeff_X j)]
  split_ifs with h
  · subst h; rw [pderiv_X_self, mul_one]
  · rw [pderiv_X_of_ne h, mul_zero]

/-- The derivative of the chord relation: `∂₁λ (T₂ - T₁) = λ - ω'(T₁)`. -/
theorem pderiv_zero_chordSlope_mul (A : R) :
    pderiv 0 (chordSlope A) * (MvPowerSeries.X 1 - MvPowerSeries.X 0) = chordSlope A -
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R)
        (PowerSeries.derivative (R := R) (omegaSeries A)) := by
  have := congrArg (pderiv 0) (chordSlope_mul_sub A)
  rw [Derivation.leibniz, map_sub, map_sub, pderiv_X_self, pderiv_X_of_ne one_ne_zero,
    omegaFst_eq_subst, omegaSnd, pderiv_subst_X, pderiv_subst_X, ite_eq_left rfl, ite_eq_right one_ne_zero,
    smul_eq_mul, smul_eq_mul] at this
  linear_combination this

/-- `ω'(T₁) (1 - 2A T₁ ω(T₁)) = 3T₁² + A ω(T₁)²`. -/
theorem subst_derivative_omega_mul_fst (A : R) :
    PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R)
        (PowerSeries.derivative (R := R) (omegaSeries A)) *
      (1 - 2 * MvPowerSeries.C A * MvPowerSeries.X 0 * omegaFst A) =
      3 * MvPowerSeries.X 0 ^ 2 + MvPowerSeries.C A * omegaFst A ^ 2 := by
  rw [omegaFst_eq_subst]
  exact subst_derivative_omegaSeries_mul (constantCoeff_X 0) A

end ZInQ.Mult
