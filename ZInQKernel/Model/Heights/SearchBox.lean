import ZInQKernel.Model.Heights.Search
import ZInQKernel.Model.Heights.DuplicationBounds

/-!
# The search box for small heights

Blueprint: `model/heights/search-box.md`.

Let `x ∈ K₀` with `h(x) < log 9`.
1. If `x ∈ ℚ`, then `x = p/q` with `gcd(p, q) = 1`, `|p| ≤ 8`, `1 ≤ q ≤ 8`.
2. If `x ∉ ℚ`, then `x = (-b ± k s)/(2a)` for integers with `1 ≤ a ≤ 81`, `|b| ≤ 162`, `|c| ≤ 81`,
   `gcd(a, b, c) = 1`, `b² - 4ac = 2k²`, `1 ≤ k ≤ 162`, and `a x² + b x + c = 0`.

Write `x = α/β` with `α, β ∈ ℤ[s]` coprime and `N(β) > 0`. With `M = max(1, |σ₊x|) max(1, |σ₋x|)`,
the height formula gives `N(β) M = exp(2h(x)) < 81`. The integer polynomial
`N(β) X² - Tr(α β̄) X + N(α)` vanishes at `x`; divided by its content it is `a X² + b X + c` with
`b = -2ua`, `c = a(u² - 2v²)` for `x = u + v s`, and `a M < 81`, `|b| ≤ 2aM`, `|c| ≤ aM`.
-/

namespace ZInQ

open QuadraticAlgebra

/-- A coprime fraction `x = α / β` with `N(β) > 0` (multiply by `ε`, `N(ε) = -1`, if needed). -/
theorem exists_coprime_fraction_pos (x : K0) :
    ∃ α β : Zs, IsCoprime α β ∧ 0 < QuadraticAlgebra.norm β ∧ x = Zs.toK0 α / Zs.toK0 β := by
  obtain ⟨α, β, hb, hab, rfl⟩ := exists_coprime_fraction x
  have hN : QuadraticAlgebra.norm β ≠ 0 := Zs.norm_ne_zero hb
  rcases lt_or_gt_of_ne hN with h | h
  · refine ⟨epsilonZ * α, epsilonZ * β, ?_, ?_, ?_⟩
    · obtain ⟨u, v, huv⟩ := hab
      refine ⟨u * ((epsUnit⁻¹ : Zsˣ) : Zs), v * ((epsUnit⁻¹ : Zsˣ) : Zs), ?_⟩
      have : ((epsUnit⁻¹ : Zsˣ) : Zs) * epsilonZ = 1 := by
        rw [← epsUnit_val, Units.inv_mul]
      linear_combination (u * α + v * β) * this + huv
    · rw [map_mul, norm_epsilonZ]; linarith
    · rw [map_mul, map_mul, mul_div_mul_left _ _
        (toK0_ne_zero (by rw [← epsUnit_val]; exact epsUnit.ne_zero))]
  · exact ⟨α, β, hab, h, rfl⟩

theorem abs_le_max_mul_max (p q : ℝ) : |p| ≤ max |p| 1 * max |q| 1 := by
  have h1 : |p| ≤ max |p| 1 := le_max_left _ _
  have h2 : (1 : ℝ) ≤ max |q| 1 := le_max_right _ _
  have h3 : (0 : ℝ) ≤ max |p| 1 := le_trans zero_le_one (le_max_right _ _)
  nlinarith

theorem one_le_max_mul_max (p q : ℝ) : 1 ≤ max |p| 1 * max |q| 1 := by
  have h1 : (1 : ℝ) ≤ max |p| 1 := le_max_right _ _
  have h2 : (1 : ℝ) ≤ max |q| 1 := le_max_right _ _
  nlinarith

theorem abs_mul_le_max_mul_max (p q : ℝ) : |p| * |q| ≤ max |p| 1 * max |q| 1 :=
  mul_le_mul (le_max_left _ _) (le_max_left _ _) (abs_nonneg _)
    (le_trans zero_le_one (le_max_right _ _))

theorem max_abs_mul_eq (σ : K0 →+* ℝ) {x β : K0} :
    max |σ x * σ β| |σ β| = |σ β| * max |σ x| 1 := by
  rw [mul_max_of_nonneg _ _ (abs_nonneg _), mul_one, abs_mul, mul_comm]

/-- `N(β) · max(1, |σ₊x|) max(1, |σ₋x|) = exp(2 h(x)) < 81` for `x = α/β`, `h(x) < log 9`. -/
theorem norm_mul_M_lt {α β : Zs} (hab : IsCoprime α β) (hN : 0 < QuadraticAlgebra.norm β)
    (hx : hK0 (Zs.toK0 α / Zs.toK0 β) < Real.log 9) :
    ((QuadraticAlgebra.norm β : ℤ) : ℝ) * (max |K0.embPlus (Zs.toK0 α / Zs.toK0 β)| 1 *
      max |K0.embMinus (Zs.toK0 α / Zs.toK0 β)| 1) < 81 := by
  have hb : β ≠ 0 := by rintro rfl; simp at hN
  have hB := toK0_ne_zero hb
  have he := exp_two_mul_hK0_div_of_isCoprime hab
  have h81 : Real.exp (2 * hK0 (Zs.toK0 α / Zs.toK0 β)) < 81 := by
    calc Real.exp (2 * hK0 (Zs.toK0 α / Zs.toK0 β)) < Real.exp (2 * Real.log 9) :=
          Real.exp_lt_exp.mpr (by linarith)
      _ = 81 := by
          rw [show (2 : ℝ) * Real.log 9 = Real.log (9 ^ 2) by rw [Real.log_pow]; push_cast; ring,
            Real.exp_log (by norm_num)]; norm_num
  rw [he] at h81
  have hσ : ∀ σ : K0 →+* ℝ, σ (Zs.toK0 α) = σ (Zs.toK0 α / Zs.toK0 β) * σ (Zs.toK0 β) := by
    intro σ; rw [← map_mul, div_mul_cancel₀ _ hB]
  rw [hσ K0.embPlus, hσ K0.embMinus, max_abs_mul_eq, max_abs_mul_eq] at h81
  have hn : ((QuadraticAlgebra.norm β : ℤ) : ℝ) =
      |K0.embPlus (Zs.toK0 β)| * |K0.embMinus (Zs.toK0 β)| := by
    rw [← abs_norm_eq, abs_of_pos (by exact_mod_cast hN)]
  rw [hn]
  linarith

theorem K0_ratCast_mul (q : ℚ) (x : K0) : (q : K0) * x = ⟨q * x.re, q * x.im⟩ := by
  ext <;> simp

/-- **The search box.** If `h(x) < log 9` then either `x = p/q ∈ ℚ` with `gcd(p, q) = 1`,
`|p| ≤ 8`, `1 ≤ q ≤ 8`, or `x ∉ ℚ` and `x = (-b ± k s)/(2a)` for a primitive integer quadratic
`a X² + b X + c` vanishing at `x` with `1 ≤ a ≤ 81`, `|b| ≤ 162`, `|c| ≤ 81`, `b² - 4ac = 2k²` and
`1 ≤ k ≤ 162`. -/
theorem search_box (x : K0) (hx : hK0 x < Real.log 9) :
    (x.im = 0 → ∃ p q : ℤ, Int.gcd p q = 1 ∧ |p| ≤ 8 ∧ 1 ≤ q ∧ q ≤ 8 ∧
      x = (((p : ℚ) / q : ℚ) : K0)) ∧
    (x.im ≠ 0 → ∃ a b c k : ℤ, 1 ≤ a ∧ a ≤ 81 ∧ |b| ≤ 162 ∧ |c| ≤ 81 ∧
      Int.gcd (Int.gcd a b) c = 1 ∧ b ^ 2 - 4 * a * c = 2 * k ^ 2 ∧ 1 ≤ k ∧ k ≤ 162 ∧
      (x = ⟨((-b : ℤ) : ℚ) / (2 * (a : ℚ)), (k : ℚ) / (2 * (a : ℚ))⟩ ∨
        x = ⟨((-b : ℤ) : ℚ) / (2 * (a : ℚ)), ((-k : ℤ) : ℚ) / (2 * (a : ℚ))⟩) ∧
      (a : K0) * x ^ 2 + (b : K0) * x + (c : K0) = 0) := by
  constructor
  · intro hv
    have hxr : x = ((x.re : ℚ) : K0) := by ext <;> simp [hv]
    rw [hxr, hK0_ratCast] at hx
    have hpos : (0 : ℝ) < max |((x.re.num : ℤ) : ℝ)| ((x.re.den : ℕ) : ℝ) :=
      lt_max_of_lt_right (by exact_mod_cast x.re.den_pos)
    have hlt := (Real.log_lt_log_iff hpos (by norm_num)).mp hx
    have h1 : |((x.re.num : ℤ) : ℝ)| < 9 := lt_of_le_of_lt (le_max_left _ _) hlt
    have h2 : ((x.re.den : ℕ) : ℝ) < 9 := lt_of_le_of_lt (le_max_right _ _) hlt
    have h1' : |x.re.num| < 9 := by rw [← Int.cast_abs] at h1; exact_mod_cast h1
    have h2' : x.re.den < 9 := by exact_mod_cast h2
    refine ⟨x.re.num, x.re.den, ?_, by omega, by exact_mod_cast x.re.den_pos, by omega, ?_⟩
    · rw [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast]; exact x.re.reduced
    · rw [hxr]; congr 1; push_cast; exact (Rat.num_div_den _).symm
  · intro hv
    obtain ⟨α, β, hab, hN, hxab⟩ := exists_coprime_fraction_pos x
    set A0 : ℤ := QuadraticAlgebra.norm β with hA0
    set γ : Zs := α * star β with hγ
    set u : ℚ := x.re
    set v : ℚ := x.im
    have hb0 : β ≠ 0 := by rintro rfl; simp [hA0] at hN
    have hB := toK0_ne_zero hb0
    -- `x · N(β) = α β̄`
    have hxA : x * ((A0 : ℚ) : K0) = Zs.toK0 γ := by
      have : ((A0 : ℚ) : K0) = Zs.toK0 β * star (Zs.toK0 β) := by
        rw [K0.mul_star_eq_norm, Zs.norm_toK0]; rfl
      rw [this, hxab, hγ, map_mul, toK0_star]; field_simp
    have hP : u * A0 = γ.re := by
      have := congrArg QuadraticAlgebra.re hxA
      rw [mul_comm, K0_ratCast_mul] at this; simpa [mul_comm] using this
    have hQ : v * A0 = γ.im := by
      have := congrArg QuadraticAlgebra.im hxA
      rw [mul_comm, K0_ratCast_mul] at this; simpa [mul_comm] using this
    have hNγ : (γ.re : ℤ) ^ 2 - 2 * γ.im ^ 2 = QuadraticAlgebra.norm α * A0 := by
      rw [← Zs.norm_eq, hγ, map_mul, QuadraticAlgebra.norm_star]
    have hA0q : (0 : ℚ) < A0 := by exact_mod_cast hN
    -- the integer polynomial `A0 X² + B0 X + C0` and its content `g`
    set B0 : ℤ := -2 * γ.re
    set C0 : ℤ := QuadraticAlgebra.norm α
    set g : ℕ := Int.gcd (Int.gcd A0 B0) C0 with hg
    have hg0 : 0 < g := Int.gcd_pos_of_ne_zero_left _
      (by rw [Ne, Nat.cast_eq_zero]; exact (Int.gcd_pos_of_ne_zero_left _ hN.ne').ne')
    have hgA : (g : ℤ) ∣ A0 := dvd_trans (Int.gcd_dvd_left _ _) (Int.gcd_dvd_left _ _)
    have hgB : (g : ℤ) ∣ B0 := dvd_trans (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
    have hgC : (g : ℤ) ∣ C0 := Int.gcd_dvd_right _ _
    obtain ⟨a, ha⟩ := hgA
    obtain ⟨b, hb⟩ := hgB
    obtain ⟨c, hc⟩ := hgC
    have hgq : (0 : ℚ) < g := by exact_mod_cast hg0
    have hgz : (0 : ℤ) < g := by exact_mod_cast hg0
    have ha1 : 1 ≤ a := by
      have : 0 < (g : ℤ) * a := by rw [← ha]; exact hN
      have := pos_of_mul_pos_right this hgz.le
      omega
    -- primitivity
    have hprim : Int.gcd (Int.gcd a b) c = 1 := by
      have e1 : a = A0 / g := by rw [ha, Int.mul_ediv_cancel_left _ hgz.ne']
      have e2 : b = B0 / g := by rw [hb, Int.mul_ediv_cancel_left _ hgz.ne']
      have e3 : c = C0 / g := by rw [hc, Int.mul_ediv_cancel_left _ hgz.ne']
      rw [e1, e2, e3, Int.gcd_ediv ⟨a, ha⟩ ⟨b, hb⟩, Int.natAbs_natCast, Int.natCast_ediv]
      rw [Int.gcd_ediv (Int.gcd_dvd_left _ _) ⟨c, hc⟩, Int.natAbs_natCast, ← hg,
        Nat.div_self hg0]
    -- the rational relations `b = -2ua`, `c = a(u² - 2v²)`
    have hbq : (b : ℚ) = -2 * u * a := by
      have h1 : (g : ℚ) * b = -2 * (γ.re : ℚ) := by exact_mod_cast hb.symm
      have h2 : ((A0 : ℤ) : ℚ) = g * a := by exact_mod_cast ha
      rw [← hP, h2] at h1
      have := mul_left_cancel₀ hgq.ne' (by linear_combination h1 : (g : ℚ) * b = g * (-2 * u * a))
      exact this
    have hcq : (c : ℚ) = a * (u ^ 2 - 2 * v ^ 2) := by
      have h1 : (g : ℚ) * c = ((QuadraticAlgebra.norm α : ℤ) : ℚ) := by exact_mod_cast hc.symm
      have h2 : ((A0 : ℤ) : ℚ) = g * a := by exact_mod_cast ha
      have h3 : ((γ.re : ℤ) : ℚ) ^ 2 - 2 * (γ.im : ℚ) ^ 2 = ((QuadraticAlgebra.norm α : ℤ) : ℚ) * A0 := by
        exact_mod_cast hNγ
      rw [← hP, ← hQ] at h3
      have h4 : ((QuadraticAlgebra.norm α : ℤ) : ℚ) = A0 * (u ^ 2 - 2 * v ^ 2) := by
        have := mul_right_cancel₀ hA0q.ne' (by linear_combination h3 :
          (A0 * (u ^ 2 - 2 * v ^ 2)) * (A0 : ℚ) = ((QuadraticAlgebra.norm α : ℤ) : ℚ) * A0)
        exact this.symm
      rw [h4, h2] at h1
      exact mul_left_cancel₀ hgq.ne' (by linear_combination h1)
    -- the archimedean bounds
    have hM := norm_mul_M_lt hab hN (hxab ▸ hx)
    rw [← hxab] at hM
    set M : ℝ := max |K0.embPlus x| 1 * max |K0.embMinus x| 1 with hMdef
    have hM1 : 1 ≤ M := one_le_max_mul_max _ _
    have haA : (a : ℝ) ≤ (A0 : ℝ) := by
      have : (A0 : ℤ) = g * a := ha
      have : a ≤ A0 := by rw [this]; exact le_mul_of_one_le_left (by omega) (by omega)
      exact_mod_cast this
    have haM : (a : ℝ) * M < 81 := by nlinarith
    have hplus : K0.embPlus x = (u : ℝ) + (v : ℝ) * Real.sqrt 2 := K0.embPlus_apply x
    have hminus : K0.embMinus x = (u : ℝ) - (v : ℝ) * Real.sqrt 2 := K0.embMinus_apply x
    have hbr : (b : ℝ) = -2 * (u : ℝ) * a := by exact_mod_cast hbq
    have hcr : (c : ℝ) = a * ((u : ℝ) ^ 2 - 2 * (v : ℝ) ^ 2) := by exact_mod_cast hcq
    have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have ha0r : (0 : ℝ) < a := by exact_mod_cast ha1
    have hbM : |(b : ℝ)| ≤ 2 * a * M := by
      have e : |(b : ℝ)| = a * |K0.embPlus x + K0.embMinus x| := by
        rw [hbr, hplus, hminus, show (u : ℝ) + v * Real.sqrt 2 + (u - v * Real.sqrt 2) = 2 * u by
          ring, abs_mul, abs_mul, abs_mul, abs_of_pos ha0r]
        norm_num; ring
      rw [e]
      have := abs_add_le (K0.embPlus x) (K0.embMinus x)
      have h1 := abs_le_max_mul_max (K0.embPlus x) (K0.embMinus x)
      have h2 := abs_le_max_mul_max (K0.embMinus x) (K0.embPlus x)
      rw [mul_comm] at h2
      nlinarith
    have hcM : |(c : ℝ)| ≤ a * M := by
      have e : |(c : ℝ)| = a * (|K0.embPlus x| * |K0.embMinus x|) := by
        rw [hcr, ← abs_mul, hplus, hminus, abs_mul, abs_of_pos ha0r]
        congr 2; linear_combination (v : ℝ) ^ 2 * hs2
      rw [e]
      exact mul_le_mul_of_nonneg_left (abs_mul_le_max_mul_max _ _) ha0r.le
    have ha80 : a ≤ 80 := by
      have : (a : ℝ) < 81 := by nlinarith
      have : a < 81 := by exact_mod_cast this
      omega
    have hb161 : |b| ≤ 161 := by
      have : |(b : ℝ)| < 162 := by nlinarith
      have : |b| < 162 := by rw [← Int.cast_abs] at this; exact_mod_cast this
      omega
    have hc80 : |c| ≤ 80 := by
      have : |(c : ℝ)| < 81 := by nlinarith
      have : |c| < 81 := by rw [← Int.cast_abs] at this; exact_mod_cast this
      omega
    -- the discriminant `b² - 4ac = 8 a² v² = 2 k²`
    have hD : ((b ^ 2 - 4 * a * c : ℤ) : ℚ) = 8 * a ^ 2 * v ^ 2 := by
      push_cast; rw [hbq, hcq]; ring
    obtain ⟨W, hW⟩ := Search.exists_int_of_rat_sq (n := 2 * (b ^ 2 - 4 * a * c)) (q := 4 * a * v)
      (by push_cast at hD ⊢; rw [hD]; ring)
    have hWv : ((W : ℚ)) ^ 2 = (4 * a * v) ^ 2 := by
      have : ((2 * (b ^ 2 - 4 * a * c) : ℤ) : ℚ) = (W : ℚ) * W := by rw [hW]; push_cast; ring
      push_cast at this hD
      rw [hD] at this; linear_combination -this
    have hWe : Even W := by
      have : Even (W * W) := ⟨b ^ 2 - 4 * a * c, by rw [← hW]; ring⟩
      exact (Int.even_mul.mp this).elim id id
    obtain ⟨K, rfl⟩ := hWe
    have hKv : (K : ℚ) = 2 * a * v ∨ (K : ℚ) = -(2 * a * v) := by
      have : ((K : ℚ)) ^ 2 = (2 * a * v) ^ 2 := by push_cast at hWv; linear_combination hWv / 4
      exact sq_eq_sq_iff_eq_or_eq_neg.mp this
    have hK2 : b ^ 2 - 4 * a * c = 2 * K ^ 2 := by
      have : 2 * (b ^ 2 - 4 * a * c) = 2 * (2 * K ^ 2) := by rw [hW]; ring
      linarith
    have hK0' : K ≠ 0 := by
      rintro rfl
      have hv0 : v = 0 := by
        rcases hKv with h | h <;> push_cast at h <;>
          · have : (2 * a : ℚ) ≠ 0 := by positivity
            rcases mul_eq_zero.mp (show (2 * (a : ℚ)) * v = 0 by linarith) with h' | h'
            · exact absurd h' this
            · exact h'
      exact hv hv0
    have hk162 : |K| ≤ 161 := by
      have hb2 : b ^ 2 ≤ 161 ^ 2 := by
        have := abs_le.mp hb161; nlinarith
      have hac : -(4 * a * c) ≤ 4 * 80 * 80 := by
        have := abs_le.mp hc80; nlinarith
      have : K ^ 2 < 162 ^ 2 := by nlinarith
      have := abs_lt_of_sq_lt_sq' this (by norm_num)
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    refine ⟨a, b, c, |K|, ha1, by omega, by omega, by omega, hprim, by rw [sq_abs]; exact hK2,
      Int.one_le_abs hK0', by omega, ?_, ?_⟩
    · have hu : u = ((-b : ℤ) : ℚ) / (2 * (a : ℚ)) := by
        push_cast; rw [hbq]; field_simp
      have hxuv : x = ⟨u, v⟩ := rfl
      rcases le_or_gt 0 K with hK | hK
      · rw [abs_of_nonneg hK]
        rcases hKv with h | h
        · left; rw [hxuv, hu]; congr 1; rw [h]; field_simp
        · right; rw [hxuv, hu]; congr 1; push_cast; rw [h]; field_simp
      · rw [abs_of_neg hK]
        rcases hKv with h | h
        · right; rw [hxuv, hu]; congr 1; push_cast; rw [h]; field_simp
        · left; rw [hxuv, hu]; congr 1; push_cast; rw [h]; field_simp
    · have hxuv : x = ⟨u, v⟩ := rfl
      rw [hxuv]
      ext
      · simp [pow_two]; rw [hbq, hcq]; ring
      · simp [pow_two]; rw [hbq]; ring

/-- Points of height `< log 9` have their abscissa in the finite search set `𝒳₁ ∪ 𝒳₂`. -/
theorem mem_search_of_hK0_lt (x : K0) (hx : hK0 x < Real.log 9) :
    x ∈ searchX1.image (fun r : ℚ => (r : K0)) ∪ searchX2 := by
  obtain ⟨h1, h2⟩ := search_box x hx
  by_cases hv : x.im = 0
  · obtain ⟨p, q, hpq, hp, hq1, hq2, rfl⟩ := h1 hv
    apply Finset.mem_union_left
    refine Finset.mem_image.mpr ⟨(p : ℚ) / q, ?_, rfl⟩
    simp only [searchX1, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    have := abs_le.mp hp
    exact ⟨(p, q), ⟨⟨⟨by omega, by omega⟩, ⟨hq1, by omega⟩⟩, hpq⟩, rfl⟩
  · obtain ⟨a, b, c, k, ha1, ha2, hb, hc, hprim, hk, hk1, hk2, hroot, -⟩ := h2 hv
    apply Finset.mem_union_right
    have hQ : (a, b, c) ∈ searchQ := by
      simp only [searchQ, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨⟨ha1, ha2⟩, abs_le.mp hb, abs_le.mp hc⟩, hprim, k, ⟨hk1, hk2⟩, hk⟩
    have hs : Int.sqrt ((b ^ 2 - 4 * a * c) / 2) = k := by
      rw [hk, Int.mul_ediv_cancel_left _ (by norm_num), pow_two, Int.sqrt_eq]
      omega
    simp only [searchX2, Finset.mem_image, Finset.mem_product, Finset.mem_insert,
      Finset.mem_singleton]
    rcases hroot with h | h
    · refine ⟨((a, b, c), 1), ⟨hQ, Or.inl rfl⟩, ?_⟩
      simp only [qRoot, hs, one_mul]
      exact h.symm
    · refine ⟨((a, b, c), -1), ⟨hQ, Or.inr rfl⟩, ?_⟩
      simp only [qRoot, hs, neg_one_mul]
      exact h.symm

/-- Combining the search box with the finite search: an affine point `S = (x, y)` of `C(K₀)` with
`h_x(S) < log 9` has `x ∈ {0, δ, -δ, 1 + s, 23 - 17s, 2 + 4s, (5 - 4s)/2}`. -/
theorem small_point_abscissa {x y : K0} (h : curveC.toAffine.Nonsingular x y)
    (hS : hx (.some x y h) < Real.log 9) : x ∈ smallSurvivors := by
  rw [hx_some] at hS
  have hmem := mem_search_of_hK0_lt x hS
  have hsq : IsSquare (fC x) := isSquare_fC_of_point h
  rcases Finset.mem_union.mp hmem with h1 | h2
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp h1
    exact (isSquare_fC_iff_of_mem_searchX1 hr).mp hsq
  · exact (isSquare_fC_iff_of_mem_searchX2 h2).mp hsq

end ZInQ
