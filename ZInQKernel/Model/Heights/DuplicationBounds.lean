import ZInQKernel.Model.Heights.CommonDivisor
import ZInQKernel.Model.Heights.Formula

/-!
# Height bounds for doubling on `C`

Blueprint: `model/heights/duplication-height-bounds.md`.

For every `T ∈ C(K₀)`: `4 h_x(T) - log 392 ≤ h_x([2]T) ≤ 4 h_x(T) + log 676`.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine

/-- Every element of `K₀` is a fraction `a / b` with `a, b ∈ ℤ[s]` coprime, `b ≠ 0`. -/
theorem exists_coprime_fraction (x : K0) :
    ∃ a b : Zs, b ≠ 0 ∧ IsCoprime a b ∧ x = Zs.toK0 a / Zs.toK0 b := by
  obtain ⟨a, ⟨b, hb⟩, hab, rfl⟩ := IsFractionRing.exists_reduced_fraction Zs (K := K0) x
  exact ⟨a, b, nonZeroDivisors.ne_zero hb, hab.isCoprime, (IsFractionRing.mk'_eq_div _)⟩

/-- `h(δ) = ½ log 7`. -/
theorem hK0_delta : hK0 delta = Real.log 7 / 2 := by
  have hcop : IsCoprime deltaZ 1 := isCoprime_one_right
  have h := hK0_div_of_isCoprime hcop
  rw [map_one, div_one, toK0_deltaZ] at h
  rw [h]; simp only [map_one, embPlus_delta, embMinus_delta, abs_one]
  have h1 := sqrt_two_lt_two
  have h0 := Real.sqrt_nonneg 2
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [abs_of_pos (by linarith), abs_of_pos (by linarith), max_eq_left (by linarith),
    max_eq_left (by linarith), ← Real.log_mul (by linarith) (by linarith)]
  congr 2
  nlinarith

/-- The two-torsion case: `4 h(x) ≤ log 392` for `x ∈ {0, δ, -δ}`. -/
theorem four_mul_hK0_le_of_two_torsion {x : K0} (hx : x = 0 ∨ x = delta ∨ x = -delta) :
    4 * hK0 x ≤ Real.log 392 := by
  have hd : 4 * hK0 delta ≤ Real.log 392 := by
    rw [hK0_delta]
    have : 2 * Real.log 7 = Real.log 49 := by
      rw [show (49 : ℝ) = 7 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have h2 : Real.log 49 ≤ Real.log 392 := Real.log_le_log (by norm_num) (by norm_num)
    linarith
  rcases hx with rfl | rfl | rfl
  · simp; exact Real.log_nonneg (by norm_num)
  · exact hd
  · rw [hK0_neg]; exact hd

/-- **Height bounds for doubling.** -/
theorem hx_two_smul_bounds (T : curveC.toAffine.Point) :
    4 * hx T - Real.log 392 ≤ hx (2 • T) ∧ hx (2 • T) ≤ 4 * hx T + Real.log 676 := by
  have h392 : 0 ≤ Real.log 392 := Real.log_nonneg (by norm_num)
  have h676 : 0 ≤ Real.log 676 := Real.log_nonneg (by norm_num)
  rcases T with _ | ⟨x, y, h⟩
  · simp only [← Point.zero_def, nsmul_zero, hx_zero, mul_zero, zero_sub, zero_add]
    constructor <;> linarith
  by_cases hy : y = 0
  · rw [two_smul_C_of_y_eq_zero h hy, hx_zero, hx_some]
    have he := (curveC_equation_iff x y).mp h.1
    rw [hy] at he
    have hx3 : x * (x - delta) * (x + delta) = 0 := by linear_combination -he
    have hx' : x = 0 ∨ x = delta ∨ x = -delta := by
      rcases mul_eq_zero.mp hx3 with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (Or.inl (sub_eq_zero.mp h2))
      · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h1))
    have := four_mul_hK0_le_of_two_torsion hx'
    have := hK0_nonneg x
    constructor <;> linarith
  obtain ⟨a, b, hb, hab, hxab⟩ := exists_coprime_fraction x
  obtain ⟨hG, y', h', e⟩ := x_two_smul_C h hy hb hxab
  rw [e, hx_some, hx_some, hxab]
  set g := EuclideanDomain.gcd (F2 a b) (G2 a b) with hgdef
  have hgF : g ∣ F2 a b := EuclideanDomain.gcd_dvd_left _ _
  have hgG : g ∣ G2 a b := EuclideanDomain.gcd_dvd_right _ _
  have hg : ∀ d, d ∣ F2 a b → d ∣ G2 a b → d ∣ g := fun d h1 h2 => EuclideanDomain.dvd_gcd h1 h2
  have hG0 : G2 a b ≠ 0 := hG
  rw [hK0_div _ _ hG0 g hgF hgG hg, hK0_div_of_isCoprime hab]
  obtain ⟨-, -, -, hN⟩ := duplication_common_divisor hab hgF hgG hg (Or.inr hG0)
  have hg0 : g ≠ 0 := by rintro h0; rw [h0] at hgG; exact hG0 (zero_dvd_iff.mp hgG)
  -- bounds on `log |N g|`
  have hN1 : (1 : ℝ) ≤ |((QuadraticAlgebra.norm g : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (Zs.norm_ne_zero hg0)
  have hN2 : |((QuadraticAlgebra.norm g : ℤ) : ℝ)| ≤ 392 ^ 2 := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast hN
  have hlN0 : 0 ≤ Real.log |((QuadraticAlgebra.norm g : ℤ) : ℝ)| := Real.log_nonneg hN1
  have hlN2 : Real.log |((QuadraticAlgebra.norm g : ℤ) : ℝ)| ≤ 2 * Real.log 392 := by
    have := Real.log_le_log (by linarith) hN2
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  -- archimedean bounds
  have arch : ∀ σ : K0 →+* ℝ, (σ = K0.embPlus ∨ σ = K0.embMinus) →
      4 * Real.log (max |σ (Zs.toK0 a)| |σ (Zs.toK0 b)|) ≤
        Real.log (max |σ (Zs.toK0 (F2 a b))| |σ (Zs.toK0 (G2 a b))|) ∧
      Real.log (max |σ (Zs.toK0 (F2 a b))| |σ (Zs.toK0 (G2 a b))|) ≤
        Real.log 676 + 4 * Real.log (max |σ (Zs.toK0 a)| |σ (Zs.toK0 b)|) := by
    intro σ hσ
    have hM := max_abs_pos_of_isCoprime σ hab
    obtain ⟨h1, h2⟩ := duplication_bounds_emb σ hσ (Zs.toK0 a) (Zs.toK0 b)
    rw [← toK0_F2, ← toK0_G2] at h1 h2
    have hM4 : 0 < max |σ (Zs.toK0 a)| |σ (Zs.toK0 b)| ^ 4 := by positivity
    constructor
    · have := Real.log_le_log hM4 h1
      rwa [Real.log_pow, Nat.cast_ofNat] at this
    · have := Real.log_le_log (lt_of_lt_of_le hM4 h1) h2
      rwa [Real.log_mul (by norm_num) hM4.ne', Real.log_pow, Nat.cast_ofNat] at this
  obtain ⟨p1, p2⟩ := arch K0.embPlus (Or.inl rfl)
  obtain ⟨m1, m2⟩ := arch K0.embMinus (Or.inr rfl)
  constructor <;> linarith

end ZInQ
