import ZInQKernel.Contrib.CloudB3RC53.NewformS13.QExpDifferential
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Reading translation S1, function-field part: the cusp `∞` of `ℚ(j, j_M)`

Translation S1 of the reduction of `NewformPeriodsRational`: "the standard model of `X₀(M)` over
`ℚ`, its rational cusp `∞`, and its function field `ℚ(j, j(Mz))` embedded in `ℚ((q))` by the
`q`-expansion at `∞`". In the function-field language of the vendored algebraic-curve library
(`AlgebraicCurve.Place`), this file constructs the cusp `∞` of `F = ℚ(j, j_M)`:

* `vInf M`: the `q`-adic valuation of `ℚ((q))` restricted to `F` (the order of the `q`-expansion
  at `∞`);
* `jInvariantQ_not_mem_powerSeries`: `j` has a pole at `∞` (it is not a power series in `q`);
* **`cuspInf M : AlgebraicCurve.Place ℚ F`**: the place of `F` at `∞` (a discrete valuation
  subring containing `ℚ`, proper since `j` has a pole);
* **`cuspInf_deg`**: `∞` is a RATIONAL place: its residue field is `ℚ` (degree one; the residue of
  a function regular at `∞` is the constant term of its `q`-expansion).

The scheme `X₀(M)` and the identification of `F` with its function field remain outside this
file.

All statements are definitions or PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.NewformS13

open ZInQ.Contrib.RC53Assist.NewformPeriods
open scoped WithZero

variable (M : ℕ) [NeZero M]

/-! ### `j` has a pole at `∞` -/

theorem jInvariantQ_not_mem_powerSeries :
    ¬ ∃ J : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ J = jInvariantQ := by
  rintro ⟨J, hJ⟩
  have hD0 : HahnSeries.ofPowerSeries ℤ ℚ (eisensteinE4Q ^ 3 - eisensteinE6Q ^ 2) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun z : LaurentSeries ℚ => z.coeff ((1 : ℕ) : ℤ)) h0
    simp only [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.coeff_zero,
      eisenstein_disc_coeff_one] at h1
    norm_num at h1
  have hD : (HahnSeries.ofPowerSeries ℤ ℚ eisensteinE4Q) ^ 3 -
      (HahnSeries.ofPowerSeries ℤ ℚ eisensteinE6Q) ^ 2 =
      HahnSeries.ofPowerSeries ℤ ℚ (eisensteinE4Q ^ 3 - eisensteinE6Q ^ 2) := by
    rw [map_sub, map_pow, map_pow]
  have hN : (1728 : LaurentSeries ℚ) * (HahnSeries.ofPowerSeries ℤ ℚ eisensteinE4Q) ^ 3 =
      HahnSeries.ofPowerSeries ℤ ℚ (1728 * eisensteinE4Q ^ 3) := by
    rw [map_mul, map_pow, map_ofNat]
  have hj : jInvariantQ * HahnSeries.ofPowerSeries ℤ ℚ (eisensteinE4Q ^ 3 - eisensteinE6Q ^ 2) =
      HahnSeries.ofPowerSeries ℤ ℚ (1728 * eisensteinE4Q ^ 3) := by
    rw [jInvariantQ, hD, div_mul_cancel₀ _ hD0, hN]
  rw [← hJ, ← map_mul] at hj
  have h1 := congrArg (PowerSeries.coeff 0) (HahnSeries.ofPowerSeries_injective hj)
  rw [eisenstein_num_coeff_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply (eisensteinE4Q ^ 3 - eisensteinE6Q ^ 2),
    eisenstein_disc_coeff_zero, mul_zero] at h1
  norm_num at h1

/-! ### The valuation at `∞` -/

/-- **The valuation of `F` at the cusp `∞`**: the `q`-adic valuation of the `q`-expansion. -/
def vInf : Valuation (FQ M) ℤᵐ⁰ :=
  (Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).comap (algebraMap (FQ M) (LaurentSeries ℚ))

theorem vInf_le_one_iff (f : FQ M) :
    vInf M f ≤ 1 ↔ ∃ F : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ F = (f : LaurentSeries ℚ) :=
  LaurentSeries.val_le_one_iff_eq_coe ℚ _

/-- `j` as an element of `F`. -/
def jF : FQ M := ⟨jInvariantQ, jInvariantQ_mem M⟩

theorem one_lt_vInf_j : 1 < vInf M (jF M) := by
  rw [← not_le, vInf_le_one_iff]
  exact jInvariantQ_not_mem_powerSeries

instance nontrivial_valueGroup : Nontrivial (vInf M : FQ M →*₀ ℤᵐ⁰).valueGroup := by
  have hne : vInf M (jF M) ≠ 0 := ne_of_gt (lt_trans zero_lt_one (one_lt_vInf_j M))
  refine ⟨⟨⟨Units.mk0 _ hne, MonoidWithZeroHom.mem_valueGroup _ ⟨jF M, rfl⟩⟩, 1, ?_⟩⟩
  intro h
  have := congrArg (fun u : (vInf M : FQ M →*₀ ℤᵐ⁰).valueGroup => ((u : ℤᵐ⁰ˣ) : ℤᵐ⁰)) h
  simp only [Units.val_mk0, OneMemClass.coe_one, Units.val_one] at this
  exact (ne_of_gt (one_lt_vInf_j M)) this

/-- **The cusp `∞` as a place of `F = ℚ(j, j_M)`.** -/
def cuspInf : AlgebraicCurve.Place ℚ (FQ M) where
  toValuationSubring := (vInf M).valuationSubring
  algebraMap_mem' a := by
    rw [Valuation.mem_valuationSubring_iff, vInf_le_one_iff]
    exact ⟨PowerSeries.C a, by simp⟩
  ne_top' h := by
    have hj : jF M ∈ (vInf M).valuationSubring := h ▸ ValuationSubring.mem_top _
    rw [Valuation.mem_valuationSubring_iff] at hj
    exact absurd hj (not_le.2 (one_lt_vInf_j M))
  isPrincipalIdealRing' := Valuation.valuationSubring_isPrincipalIdealRing (vInf M)

/-! ### The cusp `∞` is a rational place -/

theorem vInf_lt_one_of_constantCoeff (f : FQ M) (F : PowerSeries ℚ)
    (hF : HahnSeries.ofPowerSeries ℤ ℚ F = (f : LaurentSeries ℚ))
    (h0 : PowerSeries.constantCoeff F = 0) : vInf M f < 1 := by
  obtain ⟨G, hG⟩ := PowerSeries.X_dvd_iff.2 h0
  have hv : vInf M f = Valued.v (((PowerSeries.X : PowerSeries ℚ) : LaurentSeries ℚ) ^ 1) *
      Valued.v (HahnSeries.ofPowerSeries ℤ ℚ G) := by
    change Valued.v (f : LaurentSeries ℚ) = _
    rw [← hF, hG, pow_one, map_mul, map_mul]
  rw [hv, LaurentSeries.valuation_X_pow]
  have hG1 : Valued.v (HahnSeries.ofPowerSeries ℤ ℚ G) ≤ 1 :=
    (LaurentSeries.val_le_one_iff_eq_coe ℚ _).2 ⟨G, rfl⟩
  calc WithZero.exp (-((1 : ℕ) : ℤ)) * Valued.v (HahnSeries.ofPowerSeries ℤ ℚ G)
      ≤ WithZero.exp (-((1 : ℕ) : ℤ)) * 1 := by gcongr
    _ < 1 := by
      rw [mul_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num

theorem mem_maximalIdeal_of_vInf_lt_one (x : (cuspInf M).toValuationSubring)
    (hx : vInf M x < 1) : x ∈ IsLocalRing.maximalIdeal (cuspInf M).toValuationSubring := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, rfl⟩
  have hinv : vInf M ((u⁻¹ : (cuspInf M).toValuationSubring ˣ) : FQ M) ≤ 1 :=
    ((u⁻¹ : (cuspInf M).toValuationSubring ˣ) : (cuspInf M).toValuationSubring).2
  have hmul : vInf M (u : FQ M) * vInf M ((u⁻¹ : (cuspInf M).toValuationSubring ˣ) : FQ M) = 1 := by
    rw [← map_mul]
    have : ((u : (cuspInf M).toValuationSubring) : FQ M) *
        ((u⁻¹ : (cuspInf M).toValuationSubring ˣ) : FQ M) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]
      rfl
    rw [this, map_one]
  have : vInf M (u : FQ M) * vInf M ((u⁻¹ : (cuspInf M).toValuationSubring ˣ) : FQ M) < 1 :=
    calc _ ≤ vInf M (u : FQ M) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hx
  exact (ne_of_lt this) hmul

theorem algebraMap_residueField_surjective :
    Function.Surjective (algebraMap ℚ (cuspInf M).ResidueField) := by
  intro r
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  have hx : vInf M (x : FQ M) ≤ 1 := x.2
  obtain ⟨F, hF⟩ := (vInf_le_one_iff M _).1 hx
  refine ⟨PowerSeries.constantCoeff F, ?_⟩
  rw [IsScalarTower.algebraMap_apply ℚ (cuspInf M).toValuationSubring,
    IsLocalRing.ResidueField.algebraMap_eq, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff]
  refine mem_maximalIdeal_of_vInf_lt_one M _ ?_
  refine vInf_lt_one_of_constantCoeff M _ (PowerSeries.C (PowerSeries.constantCoeff F) - F) ?_ ?_
  · rw [map_sub, hF]
    simp [AlgebraicCurve.Place.coe_algebraMap]
  · simp

/-- **The cusp `∞` is a rational place of `ℚ(j, j_M)`**: degree one. -/
theorem cuspInf_deg : (cuspInf M).deg = 1 := by
  have hbij : Function.Bijective (algebraMap ℚ (cuspInf M).ResidueField) :=
    ⟨(algebraMap ℚ (cuspInf M).ResidueField).injective, algebraMap_residueField_surjective M⟩
  rw [AlgebraicCurve.Place.deg,
    ← (AlgEquiv.ofBijective (Algebra.ofId ℚ (cuspInf M).ResidueField)
      hbij).toLinearEquiv.finrank_eq,
    Module.finrank_self]

end ZInQ.Contrib.CloudB3RC53.NewformS13
