import ZInQKernel.Contrib.OneProof.RC.GlueSweep.EvenModel

/-! The witness in `EvenFamilyOutput.outer` from the actual completed
localization, using the original group basis and the same exponent. -/

namespace ZInQ.Manuscript.RC.AppE32Fixed

open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Determinant

/-- The family part of (E.5), tex 7591–7610. Characterwise bounded
denominators locate the coefficients in `Λ[1/2]`. For each coefficient
the cleared element of `Frac 𝒪` comes from the genuine `𝒪`.
Intersect these rings to obtain the witness for `EvenFamilyOutput.outer`,
with no cost proportional to the binary dimension. -/
theorem outerWitness_of_completed_coefficients {b : ℕ}
    (u : (Fin b → ZMod 2) → PowerSeries ℚ_[2]) (cE : ℕ)
    (hchar : ∀ x, InLamHalf (charEval u x))
    (hO : ∀ g (a : LambdaHalf), Rings.halfToPowerSeries a = u g →
      (2 : FractionRing OO) ^ cE * Rings.halfToFracO a ∈
        (algebraMap OO (FractionRing OO)).range) :
    ∀ g, ∃ f : ℤ → ℤ_[2], ∀ n : ℕ,
      ((f n : ℤ_[2]) : ℚ_[2]) = PowerSeries.coeff n ((2 : ℚ_[2]) ^ cE • u g) := by
  intro g
  obtain ⟨a, ha⟩ := (GlueSweep.Even.inLamHalf_iff_mem_range (u g)).mp
    (inLamHalf_of_charEval u hchar g)
  obtain ⟨A, hA⟩ := Rings.two_pow_mul_mem_lambda_of_mem_O cE a (hO g a ha)
  refine ⟨fun n => PowerSeries.coeff n.toNat A, fun n => ?_⟩
  have he := congrArg Rings.halfToPowerSeries hA
  rw [Rings.halfToPowerSeries_algebraMap, map_mul, map_pow, map_ofNat, ha] at he
  have hc := congrArg (PowerSeries.coeff n) he
  have htwo : (2 : PowerSeries ℚ_[2]) ^ cE = PowerSeries.C ((2 : ℚ_[2]) ^ cE) := by
    rw [map_pow, map_ofNat]
  rw [PowerSeries.coeff_map, htwo, PowerSeries.coeff_C_mul] at hc
  simpa only [Int.toNat_natCast, PowerSeries.coeff_smul, smul_eq_mul, PadicInt.Coe.ringHom_apply] using hc


end ZInQ.Manuscript.RC.AppE32Fixed
