import ZInQKernel.Multiplication.Local.FormalGroup
import ZInQKernel.Multiplication.Local.Valuations

/-!
# The dyadic position of `P₀`

Blueprint: `multiplication/local/generator-dyadic-numerals.md`,
`multiplication/local/dyadic-generator.md`.

`P₀ = ((1641 - 1160 s)/8, (-123720 + 87483 s)/32)` has `v_s(x) = -6`, `v_s(y) = -9`,
`v_s(z) = 3` at the prime `(s)` of `ℤ[s]`, so `P₀ ∈ E₃` and every multiple `[n]P₀` lies in the
formal neighbourhood `E₁` at `(s)` with `v_s(z([n]P₀)) ≥ 3`. The formal-neighbourhood statement
holds over `K₀` with the valuation `v_s` itself, which is how it is stated here.
-/

namespace ZInQ.Mult

open WeierstrassCurve WeierstrassCurve.Affine

/-! ### The numerals -/

/-- The closed form of the numerals: `1641`, `87483`, `145`, `15465` are odd,
`1160 = 2³ · 145` and `123720 = 2³ · 15465`. -/
theorem genP0_dyadic_numerals_closed :
    1641 % 2 = 1 ∧ 87483 % 2 = 1 ∧ 145 % 2 = 1 ∧ 15465 % 2 = 1 ∧
      1160 = 2 ^ 3 * 145 ∧ 123720 = 2 ^ 3 * 15465 := by decide

private theorem padicValNat_two_odd {n : ℕ} (h : n % 2 = 1) : padicValNat 2 n = 0 :=
  padicValNat.eq_zero_of_not_dvd (by omega)

private theorem padicValNat_two_pow_mul {k n : ℕ} (h : n % 2 = 1) :
    padicValNat 2 (2 ^ k * n) = k := by
  rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) (by omega), padicValNat.prime_pow,
    padicValNat_two_odd h, add_zero]

/-- **The `2`-adic valuations of the coordinates of `P₀`.** -/
theorem genP0_dyadic_numerals :
    padicValNat 2 1641 = 0 ∧ padicValNat 2 1160 = 3 ∧ padicValNat 2 123720 = 3 ∧
      padicValNat 2 87483 = 0 ∧ padicValNat 2 8 = 3 ∧ padicValNat 2 32 = 5 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := genP0_dyadic_numerals_closed
  refine ⟨padicValNat_two_odd h1, ?_, ?_, padicValNat_two_odd h2, ?_, ?_⟩
  · rw [h5]; exact padicValNat_two_pow_mul h3
  · rw [h6]; exact padicValNat_two_pow_mul h4
  · exact padicValNat.prime_pow (p := 2) 3
  · exact padicValNat.prime_pow (p := 2) 5

/-! ### The valuations of the coordinates at `(s)` -/

theorem vS_genX0 : vp sqrt2Z genX0 = -6 := by
  obtain ⟨h1, h2, -, -, h8, -⟩ := genP0_dyadic_numerals
  have hnum : (1641 - 1160 * sqrt2 : K0) = ⟨1641, -1160⟩ := by ext <;> simp [sqrt2]
  have hn0 : (⟨1641, -1160⟩ : K0) ≠ 0 := by
    intro h; have := congrArg QuadraticAlgebra.re h; norm_num at this
  have hvnum : vp sqrt2Z ⟨1641, -1160⟩ = 0 := by
    rw [vS_formula (by norm_num) (by norm_num), padicValRat.neg]
    rw [show ((1641 : ℚ)) = ((1641 : ℕ) : ℚ) by norm_num,
      show ((1160 : ℚ)) = ((1160 : ℕ) : ℚ) by norm_num, padicValRat.of_nat, padicValRat.of_nat,
      h1, h2]
    norm_num
  rw [genX0_eq, hnum, vp_div prime_sqrt2Z hn0 (by norm_num), hvnum,
    show (8 : K0) = ((8 : ℕ) : K0) by norm_num, vS_nat (by norm_num), h8]
  norm_num

theorem vS_genY0 : vp sqrt2Z genY0 = -9 := by
  obtain ⟨-, -, h3, h4, -, h32⟩ := genP0_dyadic_numerals
  have hnum : (-123720 + 87483 * sqrt2 : K0) = ⟨-123720, 87483⟩ := by ext <;> simp [sqrt2]
  have hn0 : (⟨-123720, 87483⟩ : K0) ≠ 0 := by
    intro h; have := congrArg QuadraticAlgebra.re h; norm_num at this
  have hvnum : vp sqrt2Z ⟨-123720, 87483⟩ = 1 := by
    rw [vS_formula (by norm_num) (by norm_num), padicValRat.neg]
    rw [show ((123720 : ℚ)) = ((123720 : ℕ) : ℚ) by norm_num,
      show ((87483 : ℚ)) = ((87483 : ℕ) : ℚ) by norm_num, padicValRat.of_nat, padicValRat.of_nat,
      h3, h4]
    norm_num
  rw [genY0_eq, hnum, vp_div prime_sqrt2Z hn0 (by norm_num), hvnum,
    show (32 : K0) = ((32 : ℕ) : K0) by norm_num, vS_nat (by norm_num), h32]
  norm_num

theorem genX0_ne_zero : genX0 ≠ 0 := by
  intro h; have := congrArg QuadraticAlgebra.re h; simp [genX0] at this

/-- The valuation at `(s)` as an additive valuation `K₀ → ℤ ∪ {∞}`. -/
noncomputable abbrev vS : AddValuation K0 (WithTop ℤ) := vP sqrt2Z prime_sqrt2Z

/-- `E` is `y² = x³ + A x` with `A = -d²`, integral at `(s)`. -/
theorem vS_genA_nonneg : 0 ≤ vS (-genD ^ 2) := by
  rw [show -genD ^ 2 = Zs.toK0 (-genDZ ^ 2) by simp]
  exact vP_toK0_nonneg _ _

/-- **The generator in the dyadic formal group**: `v_s(x(P₀)) = -6`, `v_s(y(P₀)) = -9`,
`v_s(z(P₀)) = 3`. -/
theorem genP0_val_s :
    vS genX0 = (-6 : ℤ) ∧ vS genY0 = (-9 : ℤ) ∧
      vS (zCoord (A := -genD ^ 2) genP0) = (3 : ℤ) := by
  refine ⟨by rw [vP_apply _ genX0_ne_zero, vS_genX0], by rw [vP_apply _ genY0_ne_zero, vS_genY0],
    ?_⟩
  show vS (-genX0 / genY0) = (3 : ℤ)
  rw [neg_div, vS.map_neg, val_div_coe (by rw [vP_apply _ genX0_ne_zero, vS_genX0])
    (by rw [vP_apply _ genY0_ne_zero, vS_genY0])]
  norm_num

/-- `P₀ ∈ E₃ ⊆ E₁` at `(s)`. -/
theorem genP0_mem_formalFilt_three : genP0 ∈ formalFilt (-genD ^ 2) vS_genA_nonneg 3 := by
  refine ⟨?_, ?_⟩
  · show vS genX0 < 0
    rw [genP0_val_s.1]; exact_mod_cast (show (-6 : ℤ) < 0 by norm_num)
  · rw [genP0_val_s.2.2]

/-- **Every multiple of `P₀` lies in the dyadic formal group**, with `v_s(z([n]P₀)) ≥ 3`. -/
theorem zsmul_genP0_mem_formal (n : ℤ) :
    n • genP0 ∈ W1 vS (-genD ^ 2) ∧ ((3 : ℤ) : WithTop ℤ) ≤ vS (zCoord (A := -genD ^ 2) (n • genP0)) :=
  zsmul_mem_formalFilt vS_genA_nonneg genP0_mem_formalFilt_three n

end ZInQ.Mult
