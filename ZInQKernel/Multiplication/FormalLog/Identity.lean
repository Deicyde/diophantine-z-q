import ZInQKernel.Multiplication.FormalLog.Algebra
import ZInQKernel.Multiplication.FormalLog.Relations
import ZInQKernel.Multiplication.FormalLog.InvDiff

/-!
# `log(F(T₁, T₂)) = log(T₁) + log(T₂)`

Blueprint: `multiplication/local/formal-logarithm.md`, part 1.

Over a field `F` of characteristic `0`, with `S = log' = invDiffSeries A`: both sides of the
identity have constant coefficient `0`, so it suffices that their partial derivatives agree
(`MvPowerSeries.pderiv.ext`). By the chain rule, `∂₁ log(F) = S(F) ∂₁F`, and
`S(F)(1 - 2A F ω(F)) = 1`, `S(T₁)(1 - 2A T₁ ω(T₁)) = 1` (`invDiffSeries_mul_omega`). Now
`ω(F) = λF - ν` (`subst_formalAdd_omega`: both solve `W = F³ + A F W²`, by the chord algebra
`chord_third_root`), and the chord algebra gives `∂₁F (1 - 2A T₁ ω(T₁)) = 1 - 2A F ω(F)`
(`chord_invariance`), so `∂₁ log(F) = S(T₁) = ∂₁ log(T₁)`. The case of `∂₂` is the same with
`T₁` and `T₂` exchanged (`λ` and `ν = ω₂ - λT₂` are symmetric).
-/

namespace ZInQ.Mult

open MvPowerSeries

variable {F : Type*} [Field F] [CharZero F]

local notation "T₀" => (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) F)
local notation "T₁" => (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) F)

theorem X_zero_sub_X_one_ne_zero : (T₀ - T₁) ≠ 0 := by
  intro h
  have := congrArg (coeff (Finsupp.single 0 1)) h
  classical
  have hne : (Finsupp.single (0 : Fin 2) 1) ≠ Finsupp.single 1 1 := by
    intro h'; have := congrArg (· 0) h'; simp at this
  simp [coeff_X, hne] at this

theorem X_one_sub_X_zero_ne_zero : (T₁ - T₀) ≠ 0 := by
  intro h
  exact X_zero_sub_X_one_ne_zero (by linear_combination -h)

/-- Uniqueness of the solution of `W = a³ + A a W²` with `W(0) = 0`. -/
theorem omega_unique_of_eq {σ : Type*} {A : F} {a W W' : MvPowerSeries σ F}
    (ha : constantCoeff a = 0) (hW : W = a ^ 3 + C A * a * W ^ 2)
    (hW' : W' = a ^ 3 + C A * a * W' ^ 2) : W = W' := by
  have h : (W - W') * (1 - C A * a * (W + W')) = 0 := by linear_combination hW - hW'
  have hne : (1 - C A * a * (W + W')) ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    simp [ha] at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hne)

/-- `S(a) (1 - 2A a ω(a)) = 1` for `a` with constant coefficient `0`. -/
theorem subst_invDiffSeries_mul {σ : Type*} {a : MvPowerSeries σ F} (ha : constantCoeff a = 0)
    (A : F) :
    PowerSeries.subst a (invDiffSeries A) *
      (1 - 2 * C A * a * PowerSeries.subst a (omegaSeries A)) = 1 := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have h := congrArg (PowerSeries.substAlgHom (R := F) hs) (invDiffSeries_mul_omega A)
  simp only [map_mul, map_sub, map_one, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs,
    PowerSeries.subst_C, map_ofNat] at h
  linear_combination h

theorem subst_formalAdd_omega (A : F) :
    PowerSeries.subst (formalAdd A) (omegaSeries A) =
      chordSlope A * formalAdd A - (omegaFst A - chordSlope A * T₀) := by
  have r3 := chordSlope_mul_sub A
  have h1 : chordSlope A * T₀ + (omegaFst A - chordSlope A * T₀) = omegaFst A := by ring
  have h2 : chordSlope A * T₁ + (omegaFst A - chordSlope A * T₀) = omegaSnd A := by
    linear_combination r3
  have hQ := chordQ_of_roots (A := C A) X_zero_sub_X_one_ne_zero
    (by rw [h1]; exact omegaFst_eq A) (by rw [h2]; exact omegaSnd_eq A)
  have hW := chord_third_root (A := C A) (by rw [h1]; exact omegaFst_eq A) hQ (chordInv_mul A)
    (formalAdd_eq A)
  exact omega_unique_of_eq (constantCoeff_formalAdd A)
    (subst_omegaSeries_eq (constantCoeff_formalAdd A) A) hW

omit [CharZero F] in
/-- `∂(1 + Aλ²)⁻¹ = -2Aλ (∂λ) (1 + Aλ²)⁻²`. -/
theorem pderiv_chordInv (A : F) (i : Fin 2) :
    pderiv i (chordInv A) =
      -(2 * C A * chordSlope A * pderiv i (chordSlope A) * chordInv A ^ 2) := by
  have he := chordInv_mul A
  have h := congrArg (pderiv i) he
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_add, pderiv_C, Derivation.map_one_eq_zero,
    smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero, zero_add] at h
  push_cast at h
  linear_combination (-pderiv i (chordInv A)) * he + chordInv A * h

/-- **Invariance of the differential, first variable**:
`∂₁F · (1 - 2A T₁ ω(T₁)) = 1 - 2A F ω(F)`. -/
theorem pderiv_zero_formalAdd_mul (A : F) :
    pderiv 0 (formalAdd A) * (1 - 2 * C A * T₀ * omegaFst A) =
      1 - 2 * C A * formalAdd A * PowerSeries.subst (formalAdd A) (omegaSeries A) := by
  rw [subst_formalAdd_omega]
  have r3 := chordSlope_mul_sub A
  have h1 : chordSlope A * T₀ + (omegaFst A - chordSlope A * T₀) = omegaFst A := by ring
  have h2 : chordSlope A * T₁ + (omegaFst A - chordSlope A * T₀) = omegaSnd A := by
    linear_combination r3
  have hQ := chordQ_of_roots (A := C A) X_zero_sub_X_one_ne_zero
    (by rw [h1]; exact omegaFst_eq A) (by rw [h2]; exact omegaSnd_eq A)
  have hdω₁ : pderiv 0 (omegaFst A) =
      PowerSeries.subst T₀ (PowerSeries.derivative (R := F) (omegaSeries A)) := by
    rw [omegaFst_eq_subst, pderiv_subst_X, ite_eq_left rfl]
  have hdω₂ : pderiv 0 (omegaSnd A) = 0 := by
    rw [omegaSnd, pderiv_subst_X, ite_eq_right one_ne_zero]
  have hd : pderiv 0 (chordSlope A) * (T₁ - T₀) = chordSlope A -
      PowerSeries.subst T₀ (PowerSeries.derivative (R := F) (omegaSeries A)) := by
    have := congrArg (pderiv 0) r3
    rw [Derivation.leibniz, map_sub, map_sub, pderiv_X_self, pderiv_X_of_ne one_ne_zero, hdω₁,
      hdω₂, smul_eq_mul, smul_eq_mul] at this
    linear_combination this
  have h5 := subst_derivative_omegaSeries_mul (constantCoeff_X (0 : Fin 2) (R := F)) A
  rw [← omegaFst_eq_subst, ← h1] at h5
  have h7 := chord_slope_deriv (A := C A) X_zero_sub_X_one_ne_zero hQ hd h5
  have hinv := chord_invariance (A := C A) (chordInv_mul A) (pderiv_chordInv A 0)
    (d := PowerSeries.subst T₀ (PowerSeries.derivative (R := F) (omegaSeries A)))
    (F := formalAdd A) (dF := pderiv 0 (formalAdd A))
    (by linear_combination hd) h7 (dn := pderiv 0 (omegaFst A - chordSlope A * T₀))
    (by rw [map_sub, Derivation.leibniz, pderiv_X_self, hdω₁, smul_eq_mul, smul_eq_mul]; ring)
    (formalAdd_eq A) (by
      rw [formalAdd_def]
      simp only [Derivation.leibniz, map_add, pderiv_C, pderiv_X_self, pderiv_X_of_ne one_ne_zero,
        smul_eq_mul, mul_zero, add_zero]
      rw [map_mul, map_ofNat]
      ring)
  rw [h1] at hinv
  exact hinv

/-- **Invariance of the differential, second variable**:
`∂₂F · (1 - 2A T₂ ω(T₂)) = 1 - 2A F ω(F)`. -/
theorem pderiv_one_formalAdd_mul (A : F) :
    pderiv 1 (formalAdd A) * (1 - 2 * C A * T₁ * omegaSnd A) =
      1 - 2 * C A * formalAdd A * PowerSeries.subst (formalAdd A) (omegaSeries A) := by
  rw [subst_formalAdd_omega]
  have r3 := chordSlope_mul_sub A
  have h1 : chordSlope A * T₀ + (omegaFst A - chordSlope A * T₀) = omegaFst A := by ring
  have h2 : chordSlope A * T₁ + (omegaFst A - chordSlope A * T₀) = omegaSnd A := by
    linear_combination r3
  have hQ := chordQ_of_roots (A := C A) X_one_sub_X_zero_ne_zero
    (by rw [h2]; exact omegaSnd_eq A) (by rw [h1]; exact omegaFst_eq A)
  have hdω₁ : pderiv 1 (omegaFst A) = 0 := by
    rw [omegaFst_eq_subst, pderiv_subst_X, ite_eq_right zero_ne_one]
  have hdω₂ : pderiv 1 (omegaSnd A) =
      PowerSeries.subst T₁ (PowerSeries.derivative (R := F) (omegaSeries A)) := by
    rw [omegaSnd, pderiv_subst_X, ite_eq_left rfl]
  have hd : pderiv 1 (chordSlope A) * (T₀ - T₁) = chordSlope A -
      PowerSeries.subst T₁ (PowerSeries.derivative (R := F) (omegaSeries A)) := by
    have := congrArg (pderiv 1) r3
    rw [Derivation.leibniz, map_sub, map_sub, pderiv_X_self, pderiv_X_of_ne zero_ne_one, hdω₁,
      hdω₂, smul_eq_mul, smul_eq_mul] at this
    linear_combination -this
  have h5 := subst_derivative_omegaSeries_mul (constantCoeff_X (1 : Fin 2) (R := F)) A
  rw [← omegaSnd, ← h2] at h5
  have h7 := chord_slope_deriv (A := C A) X_one_sub_X_zero_ne_zero hQ hd h5
  have hinv := chord_invariance (A := C A) (chordInv_mul A) (pderiv_chordInv A 1)
    (d := PowerSeries.subst T₁ (PowerSeries.derivative (R := F) (omegaSeries A)))
    (F := formalAdd A) (dF := pderiv 1 (formalAdd A))
    (by linear_combination hd) h7 (dn := pderiv 1 (omegaFst A - chordSlope A * T₀))
    (by
      rw [map_sub, Derivation.leibniz, pderiv_X_of_ne zero_ne_one, hdω₁, smul_eq_mul, smul_eq_mul]
      linear_combination -hd)
    (by rw [formalAdd_eq]; ring) (by
      rw [formalAdd_def]
      simp only [Derivation.leibniz, map_add, map_sub, pderiv_C, pderiv_X_self,
        pderiv_X_of_ne zero_ne_one, hdω₁, smul_eq_mul, mul_zero, add_zero, zero_add]
      rw [map_mul, map_ofNat]
      ring)
  rw [h2] at hinv
  exact hinv

/-- **`log(F(T₁, T₂)) = log(T₁) + log(T₂)`** in `F⟦T₁, T₂⟧`. -/
theorem formalLog_formalAdd_aux (A : F) :
    PowerSeries.subst (formalAdd A) (formalLog A) =
      PowerSeries.subst T₀ (formalLog A) + PowerSeries.subst T₁ (formalLog A) := by
  rw [← sub_eq_zero]
  have hF := constantCoeff_formalAdd A
  have hSF := subst_invDiffSeries_mul hF A
  have hS₀ := subst_invDiffSeries_mul (constantCoeff_X (0 : Fin 2) (R := F)) A
  have hS₁ := subst_invDiffSeries_mul (constantCoeff_X (1 : Fin 2) (R := F)) A
  rw [← omegaFst_eq_subst] at hS₀
  rw [← omegaSnd] at hS₁
  refine pderiv.ext (fun i => ?_) ?_
  · fin_cases i
    · simp only [Fin.zero_eta, map_sub, map_add, map_zero]
      rw [pderiv_subst 0 hF, pderiv_subst_X, pderiv_subst_X, ite_eq_left rfl, ite_eq_right one_ne_zero,
        derivative_formalLog_aux]
      have := pderiv_zero_formalAdd_mul A
      linear_combination (-(PowerSeries.subst (formalAdd A) (invDiffSeries A) *
        pderiv 0 (formalAdd A))) * hS₀ +
        (PowerSeries.subst (formalAdd A) (invDiffSeries A) * PowerSeries.subst T₀ (invDiffSeries A)) *
          this + PowerSeries.subst T₀ (invDiffSeries A) * hSF
    · simp only [Fin.mk_one, map_sub, map_add, map_zero]
      rw [pderiv_subst 1 hF, pderiv_subst_X, pderiv_subst_X, ite_eq_right zero_ne_one, ite_eq_left rfl,
        derivative_formalLog_aux]
      have := pderiv_one_formalAdd_mul A
      linear_combination (-(PowerSeries.subst (formalAdd A) (invDiffSeries A) *
        pderiv 1 (formalAdd A))) * hS₁ +
        (PowerSeries.subst (formalAdd A) (invDiffSeries A) * PowerSeries.subst T₁ (invDiffSeries A)) *
          this + PowerSeries.subst T₁ (invDiffSeries A) * hSF
  · have h0 : PowerSeries.constantCoeff (formalLog A) = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, formalLog, PowerSeries.coeff_mk,
        logCoeffA_zero]
    rw [map_sub, map_add, map_zero, PowerSeries.constantCoeff_subst_eq_zero hF _ h0,
      PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X 0) _ h0,
      PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X 1) _ h0]
    ring

end ZInQ.Mult
