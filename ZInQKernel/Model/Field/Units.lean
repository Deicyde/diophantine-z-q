import ZInQKernel.Model.Field.Euclidean

/-!
# Units of `ℤ[√2]`

Blueprint: `model/field/units.md`.

1. `ℤ[s]ˣ = {±εᵏ}` with `ε = 1 + s`, `ε⁻¹ = s - 1`, `N(ε) = -1`.
2. Modulo squares, every unit is in the class of exactly one of `1, -1, ε, -ε`; two units are in
   the same class iff they have the same sign vector, and the four sign vectors are
   `(+,+), (-,-), (+,-), (-,+)`.
3. A totally positive unit is the square of a unit.
-/

namespace ZInQ

open QuadraticAlgebra K0

/-- The unit `ε = 1 + s` of `ℤ[s]`, with inverse `s - 1`. -/
def epsUnit : Zsˣ where
  val := epsilonZ
  inv := ⟨-1, 1⟩
  val_inv := by ext <;> simp [epsilonZ]
  inv_val := by ext <;> simp [epsilonZ]

@[simp] theorem epsUnit_val : (epsUnit : Zs) = epsilonZ := rfl

theorem epsUnit_inv_val : ((epsUnit⁻¹ : Zsˣ) : Zs) = ⟨-1, 1⟩ := rfl

/-- `N(ε) = -1`. -/
theorem norm_epsilonZ : QuadraticAlgebra.norm epsilonZ = -1 := by
  rw [Zs.norm_eq]; simp [epsilonZ]

theorem Zs.isUnit_iff_norm {z : Zs} :
    IsUnit z ↔ QuadraticAlgebra.norm z = 1 ∨ QuadraticAlgebra.norm z = -1 := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, Int.isUnit_iff]

/-! ### The real embedding on `ℤ[s]` -/

/-- `σ₊` on `ℤ[s]`, as a group homomorphism of units. -/
noncomputable def spU : Zsˣ →* ℝˣ := Units.map (embPlus.comp Zs.toK0).toMonoidHom

theorem spU_apply (u : Zsˣ) : ((spU u : ℝˣ) : ℝ) = (u : Zs).re + (u : Zs).im * Real.sqrt 2 := by
  simp [spU, embPlus_apply]

theorem embPlus_toK0 (z : Zs) : embPlus (Zs.toK0 z) = z.re + z.im * Real.sqrt 2 := by
  simp [embPlus_apply]

theorem embMinus_toK0 (z : Zs) : embMinus (Zs.toK0 z) = z.re - z.im * Real.sqrt 2 := by
  simp [embMinus_apply]

theorem sqrt_two_bounds : 1.4 < Real.sqrt 2 ∧ Real.sqrt 2 < 1.5 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h0 := Real.sqrt_nonneg 2
  constructor <;> nlinarith

theorem spU_epsUnit : ((spU epsUnit : ℝˣ) : ℝ) = 1 + Real.sqrt 2 := by
  rw [spU_apply]; simp [epsilonZ]

/-- A unit `w` with `1 ≤ σ₊(w) < 1 + √2` is `1`. -/
theorem eq_one_of_spU_mem (w : Zsˣ) (h1 : 1 ≤ ((spU w : ℝˣ) : ℝ))
    (h2 : ((spU w : ℝˣ) : ℝ) < 1 + Real.sqrt 2) : w = 1 := by
  rw [spU_apply] at h1 h2
  set a := (w : Zs).re with ha
  set b := (w : Zs).im with hb
  have hN : a ^ 2 - 2 * b ^ 2 = 1 ∨ a ^ 2 - 2 * b ^ 2 = -1 := by
    have := Zs.isUnit_iff_norm.mp w.isUnit
    rwa [Zs.norm_eq] at this
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  obtain ⟨hs1, hs2⟩ := sqrt_two_bounds
  -- `σ₊ σ₋ = N = ±1`
  have hprod : ((a : ℝ) + b * Real.sqrt 2) * ((a : ℝ) - b * Real.sqrt 2) = 1 ∨
      ((a : ℝ) + b * Real.sqrt 2) * ((a : ℝ) - b * Real.sqrt 2) = -1 := by
    rcases hN with h | h
    · left; have : ((a ^ 2 - 2 * b ^ 2 : ℤ) : ℝ) = 1 := by exact_mod_cast h
      push_cast at this; linear_combination this - (b : ℝ) ^ 2 * hs
    · right; have : ((a ^ 2 - 2 * b ^ 2 : ℤ) : ℝ) = -1 := by exact_mod_cast h
      push_cast at this; linear_combination this - (b : ℝ) ^ 2 * hs
  -- `|σ₋| ≤ 1`
  have hm : |(a : ℝ) - b * Real.sqrt 2| ≤ 1 := by
    rw [abs_le]
    rcases hprod with h | h <;> constructor <;> nlinarith
  rw [abs_le] at hm
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have ha2 : (a : ℝ) < 2 := by linarith
  have hb0 : (0 : ℝ) ≤ b * Real.sqrt 2 := by linarith
  have hb0' : (0 : ℝ) ≤ b := by
    by_contra hneg; have := lt_of_not_ge hneg; nlinarith
  have hb2 : (b : ℝ) < 2 := by nlinarith
  have ha' : 0 ≤ a ∧ a ≤ 1 := ⟨by exact_mod_cast ha0, by
    have : (a : ℝ) < 2 := ha2; have : a < 2 := by exact_mod_cast this
    omega⟩
  have hb' : 0 ≤ b ∧ b ≤ 1 := ⟨by exact_mod_cast hb0', by
    have : b < 2 := by exact_mod_cast hb2
    omega⟩
  have hab : a = 1 ∧ b = 0 := by
    rcases ha' with ⟨ha0, ha1⟩
    rcases hb' with ⟨hb0, hb1⟩
    interval_cases a <;> interval_cases b <;>
      first | exact ⟨rfl, rfl⟩ | (simp at h2; done) | norm_num at hN
  apply Units.ext
  ext
  · simp [← ha, hab.1]
  · simp [← hb, hab.2]

/-- `ℤ[s]ˣ = {±εᵏ : k ∈ ℤ}`. -/
theorem Zs_unit_eq (u : Zsˣ) : ∃ k : ℤ, u = epsUnit ^ k ∨ u = -epsUnit ^ k := by
  -- reduce to `σ₊(u) > 0`
  have hne : ((spU u : ℝˣ) : ℝ) ≠ 0 := (spU u).ne_zero
  suffices H : ∀ v : Zsˣ, 0 < ((spU v : ℝˣ) : ℝ) → ∃ k : ℤ, v = epsUnit ^ k by
    rcases lt_or_gt_of_ne hne with h | h
    · obtain ⟨k, hk⟩ := H (-u) (by
        have : ((spU (-u) : ℝˣ) : ℝ) = -((spU u : ℝˣ) : ℝ) := by
          rw [spU_apply, spU_apply]; simp; ring
        rw [this]; linarith)
      exact ⟨k, Or.inr (by rw [← hk, neg_neg])⟩
    · obtain ⟨k, hk⟩ := H u h
      exact ⟨k, Or.inl hk⟩
  intro v hv
  have hη : (1 : ℝ) < 1 + Real.sqrt 2 := by linarith [sqrt_two_bounds.1]
  obtain ⟨k, hk1, hk2⟩ := exists_mem_Ico_zpow hv hη
  refine ⟨k, ?_⟩
  have hw : v * epsUnit ^ (-k) = 1 := by
    have hval : ((spU (v * epsUnit ^ (-k)) : ℝˣ) : ℝ) =
        ((spU v : ℝˣ) : ℝ) * (1 + Real.sqrt 2) ^ (-k) := by
      rw [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, spU_epsUnit]
    have hpos : (0 : ℝ) < (1 + Real.sqrt 2) ^ (-k) := zpow_pos (by linarith) _
    apply eq_one_of_spU_mem
    · rw [hval]
      calc (1 : ℝ) = (1 + Real.sqrt 2) ^ k * (1 + Real.sqrt 2) ^ (-k) := by
            rw [← zpow_add₀ (by linarith), add_neg_cancel, zpow_zero]
        _ ≤ _ := mul_le_mul_of_nonneg_right hk1 hpos.le
    · rw [hval]
      calc _ < (1 + Real.sqrt 2) ^ (k + 1) * (1 + Real.sqrt 2) ^ (-k) :=
            mul_lt_mul_of_pos_right hk2 hpos
        _ = 1 + Real.sqrt 2 := by
            rw [← zpow_add₀ (by linarith), show k + 1 + -k = 1 by ring, zpow_one]
  calc v = v * epsUnit ^ (-k) * epsUnit ^ k := by rw [mul_assoc, ← zpow_add, neg_add_cancel,
          zpow_zero, mul_one]
    _ = epsUnit ^ k := by rw [hw, one_mul]

/-! ### Square classes and sign vectors -/

theorem embPlus_ne_zero {z : K0} (hz : z ≠ 0) : embPlus z ≠ 0 :=
  (map_ne_zero embPlus).mpr hz

theorem embMinus_ne_zero {z : K0} (hz : z ≠ 0) : embMinus z ≠ 0 :=
  (map_ne_zero embMinus).mpr hz

/-- Multiplying by a nonzero square does not change the sign vector. -/
theorem signVector_mul_sq (z : K0) {w : K0} (hw : w ≠ 0) :
    signVector (z * w ^ 2) = signVector z := by
  have h1 : 0 < embPlus w ^ 2 := by positivity [embPlus_ne_zero hw]
  have h2 : 0 < embMinus w ^ 2 := by positivity [embMinus_ne_zero hw]
  simp only [signVector, map_mul, map_pow, sign_mul, sign_pos h1, sign_pos h2, mul_one]

theorem signVector_one : signVector 1 = (1, 1) := by simp [signVector]

theorem signVector_neg_one : signVector (-1) = (-1, -1) := by simp [signVector]

theorem signVector_epsilon : signVector epsilon = (1, -1) := by
  obtain ⟨h1, h2⟩ := sqrt_two_bounds
  simp only [signVector, embPlus_apply, embMinus_apply, epsilon, Rat.cast_one,
    one_mul]
  rw [sign_pos (by linarith), sign_neg (by linarith)]

theorem signVector_neg_epsilon : signVector (-epsilon) = (-1, 1) := by
  obtain ⟨h1, h2⟩ := sqrt_two_bounds
  simp only [signVector, map_neg, embPlus_apply, embMinus_apply, epsilon,
    Rat.cast_one, one_mul]
  rw [sign_neg (by linarith), sign_pos (by linarith)]

theorem toK0_epsUnit : Zs.toK0 (epsUnit : Zs) = epsilon := toK0_epsilonZ

/-- Every unit is `w²`, `-w²`, `ε w²` or `-ε w²` for a unit `w`. -/
theorem Zs_unit_sqClass (u : Zsˣ) :
    ∃ w : Zsˣ, u = w ^ 2 ∨ u = -w ^ 2 ∨ u = epsUnit * w ^ 2 ∨ u = -(epsUnit * w ^ 2) := by
  obtain ⟨k, hk⟩ := Zs_unit_eq u
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · refine ⟨epsUnit ^ m, ?_⟩
    have : epsUnit ^ (2 * m) = (epsUnit ^ m) ^ 2 := by rw [← zpow_natCast, ← zpow_mul]; ring_nf
    rcases hk with hk | hk
    · left; rw [hk, this]
    · right; left; rw [hk, this]
  · refine ⟨epsUnit ^ m, ?_⟩
    have : epsUnit ^ (2 * m + 1) = epsUnit * (epsUnit ^ m) ^ 2 := by
      rw [zpow_add_one, ← zpow_natCast, ← zpow_mul, mul_comm]; ring_nf
    rcases hk with hk | hk
    · right; right; left; rw [hk, this]
    · right; right; right; rw [hk, this]

theorem signVector_unit_mul_sq (u w : Zsˣ) :
    signVector (Zs.toK0 ((u * w ^ 2 : Zsˣ) : Zs)) = signVector (Zs.toK0 (u : Zs)) := by
  rw [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
  exact signVector_mul_sq _ ((map_ne_zero_iff _ Zs.toK0_injective).mpr w.ne_zero)

/-- The sign vector of a unit is determined by its square class. -/
theorem signVector_unit_sqClass (u : Zsˣ) :
    ∃ w : Zsˣ, (u = w ^ 2 ∧ signVector (Zs.toK0 (u : Zs)) = (1, 1)) ∨
      (u = -w ^ 2 ∧ signVector (Zs.toK0 (u : Zs)) = (-1, -1)) ∨
      (u = epsUnit * w ^ 2 ∧ signVector (Zs.toK0 (u : Zs)) = (1, -1)) ∨
      (u = -(epsUnit * w ^ 2) ∧ signVector (Zs.toK0 (u : Zs)) = (-1, 1)) := by
  obtain ⟨w, h | h | h | h⟩ := Zs_unit_sqClass u <;> refine ⟨w, ?_⟩
  · left; refine ⟨h, ?_⟩
    rw [h, ← one_mul (w ^ 2), signVector_unit_mul_sq]; simpa using signVector_one
  · right; left; refine ⟨h, ?_⟩
    rw [h, ← neg_one_mul (w ^ 2), signVector_unit_mul_sq]; simpa using signVector_neg_one
  · right; right; left; refine ⟨h, ?_⟩
    rw [h, signVector_unit_mul_sq, toK0_epsUnit, signVector_epsilon]
  · right; right; right; refine ⟨h, ?_⟩
    rw [h, ← neg_mul, signVector_unit_mul_sq, Units.val_neg, map_neg, toK0_epsUnit,
      signVector_neg_epsilon]

/-- Two units are in the same square class iff they have the same sign vector. In particular
the four classes of `1, -1, ε, -ε` (sign vectors `(+,+), (-,-), (+,-), (-,+)`) are distinct and
exhaust `ℤ[s]ˣ / (ℤ[s]ˣ)²`. -/
theorem unit_sqClass_iff (u v : Zsˣ) :
    (∃ w : Zsˣ, u = v * w ^ 2) ↔
      signVector (Zs.toK0 (u : Zs)) = signVector (Zs.toK0 (v : Zs)) := by
  constructor
  · rintro ⟨w, rfl⟩; exact signVector_unit_mul_sq v w
  · intro h
    obtain ⟨w₁, ⟨hu, su⟩ | ⟨hu, su⟩ | ⟨hu, su⟩ | ⟨hu, su⟩⟩ := signVector_unit_sqClass u <;>
    obtain ⟨w₂, ⟨hv, sv⟩ | ⟨hv, sv⟩ | ⟨hv, sv⟩ | ⟨hv, sv⟩⟩ := signVector_unit_sqClass v <;>
    rw [su, sv] at h <;> simp at h <;>
    · refine ⟨w₁ * w₂⁻¹, ?_⟩
      have key : w₂ ^ 2 * (w₁ * w₂⁻¹) ^ 2 = w₁ ^ 2 := by
        rw [mul_pow, inv_pow, mul_left_comm, mul_inv_cancel, mul_one]
      rw [hu, hv]; simp only [neg_mul, mul_assoc, key]

/-- A totally positive unit is the square of a unit. -/
theorem isSquare_of_totallyPositive_unit (u : Zsˣ) (h : TotallyPositive (Zs.toK0 (u : Zs))) :
    ∃ w : Zsˣ, u = w ^ 2 := by
  have h' : signVector (Zs.toK0 (u : Zs)) = signVector (Zs.toK0 ((1 : Zsˣ) : Zs)) := by
    rw [Units.val_one, map_one, signVector_one, ← totallyPositive_iff_signVector]; exact h
  obtain ⟨w, hw⟩ := (unit_sqClass_iff u 1).mpr h'
  exact ⟨w, by rw [hw, one_mul]⟩

end ZInQ
