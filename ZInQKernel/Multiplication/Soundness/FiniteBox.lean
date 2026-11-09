import ZInQKernel.Model.Field.Codes
import ZInQKernel.Multiplication.Soundness.FieldHeights
import ZInQKernel.Multiplication.Soundness.GeneratorHeight
import ZInQKernel.Multiplication.Soundness.BoxInequality
import ZInQKernel.Multiplication.Soundness.ContactSupport
import ZInQKernel.Multiplication.Certificate.HeightCertificate

/-!
# The finite-box deduction

Blueprint: `multiplication/soundness/finite-box.md` (Proposition 6.1).

The height part of the deduction (`finite_box_of_heights`): if `f = n₁n₂ - n₃ ≠ 0`, `A ≥ 1`, and
for each `i` the rational coordinates `x_{i0} = ι(nᵢ)₁`, `x_{i1} = ι(nᵢ)₂` of `x([nᵢ]P₀)` are
`a_{ij}/bᵢ` with `bᵢ ≠ 0`, where each of `a_{i0}, a_{i1}, bᵢ` is a sum of three rationals of
height at most `A |f|^{24/25}`, then `|nᵢ| < (48A)¹³`. The sum and quotient bounds, the height
bounds in `K₀`, the canonical height of multiples of `P₀`, the two explicit constants
`B₀ < 10`, `2ĥ(P₀) > 1` and the final inequality enter here.
-/

namespace ZInQ.Mult

open WeierstrassCurve WeierstrassCurve.Affine

/-- `B₀ ≥ 0`. -/
theorem heightB0_nonneg : 0 ≤ heightB0 := by
  have h1 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h3 : 0 ≤ Real.log (1 + Real.sqrt 2) := Real.log_nonneg (by linarith [Real.sqrt_nonneg 2])
  have h4 : 0 ≤ Real.log 676 := Real.log_nonneg (by norm_num)
  unfold heightB0; positivity

/-- `2 n² ĥ(P₀) ≤ h(ι(n)₁) + h(ι(n)₂) + ³⁄₂ log 2 + 2 log(1 + √2) + ⅓ log 676`. -/
theorem two_sq_canonHeightE_le (n : ℤ) :
    2 * (n : ℝ) ^ 2 * canonHeightE genP0 ≤ ratHeight (iota n 1) + ratHeight (iota n 2) +
      (3 / 2 * Real.log 2 + 2 * Real.log (1 + Real.sqrt 2) + Real.log 676 / 3) := by
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h3 : 0 ≤ Real.log (1 + Real.sqrt 2) := Real.log_nonneg (by linarith [Real.sqrt_nonneg 2])
  have h4 : 0 ≤ Real.log 676 := Real.log_nonneg (by norm_num)
  have r1 := ratHeight_nonneg (iota n 1)
  have r2 := ratHeight_nonneg (iota n 2)
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Int.cast_zero]; nlinarith
  have hQ := Mult.zsmul_genP0_ne_zero hn
  have e := canonHeightE_zsmul_genP0 n
  generalize hP : n • genP0 = P at hQ e
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hQ
  have c1 : iota n 1 = x.re := by rw [iota_def, hP]; rfl
  have c2 : iota n 2 = x.im := by rw [iota_def, hP]; rfl
  have hb := two_canonHeightE_le h
  have hε := hK0_epsilon_pow_four_mul_le x
  have hx := hK0_ratCast_add_mul_sqrt2_le x.re x.im
  rw [← K0.eq_re_add_im_mul_sqrt2] at hx
  rw [c1, c2]
  rw [e] at hb
  linarith

/-- The height part of the finite-box deduction. -/
theorem finite_box_of_heights {A : ℝ} (hA : 1 ≤ A) (n : Fin 3 → ℤ) (hf : n 0 * n 1 - n 2 ≠ 0)
    (hcert : ∀ i, ∃ a₀ a₁ b : ℚ, b ≠ 0 ∧ b * iota (n i) 1 = a₀ ∧ b * iota (n i) 2 = a₁ ∧
      ∀ Q ∈ ({a₀, a₁, b} : Set ℚ), ∃ t₁ t₂ t₃ : ℚ, t₁ + t₂ + t₃ = Q ∧
        ∀ t ∈ ({t₁, t₂, t₃} : Set ℚ),
          ratHeight t ≤ A * |((n 0 * n 1 - n 2 : ℤ) : ℝ)| ^ ((24 : ℝ) / 25)) :
    ∀ i, (|n i| : ℝ) < (48 * A) ^ 13 := by
  set F := |((n 0 * n 1 - n 2 : ℤ) : ℝ)| ^ ((24 : ℝ) / 25) with hF
  have hF0 : 0 ≤ F := by positivity
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  -- sums of three slopes
  have hsum : ∀ Q : ℚ, (∃ t₁ t₂ t₃ : ℚ, t₁ + t₂ + t₃ = Q ∧
      ∀ t ∈ ({t₁, t₂, t₃} : Set ℚ), ratHeight t ≤ A * F) → ratHeight Q ≤ 3 * A * F + Real.log 3 := by
    rintro Q ⟨t₁, t₂, t₃, rfl, ht⟩
    have := ratHeight_add3_le t₁ t₂ t₃
    have h1 := ht t₁ (by simp)
    have h2 := ht t₂ (by simp)
    have h3 := ht t₃ (by simp)
    linarith
  -- each index: `nᵢ² < 12 A F + 10`
  have hidx : ∀ i, (n i : ℝ) ^ 2 < 12 * A * F + 10 := by
    intro i
    obtain ⟨a₀, a₁, b, hb, e₀, e₁, hQ⟩ := hcert i
    have ha₀ := hsum a₀ (hQ a₀ (by simp))
    have ha₁ := hsum a₁ (hQ a₁ (by simp))
    have hbb := hsum b (hQ b (by simp))
    have hx₀ : iota (n i) 1 = a₀ / b := by rw [← e₀]; field_simp
    have hx₁ : iota (n i) 2 = a₁ / b := by rw [← e₁]; field_simp
    have d₀ := ratHeight_div_le a₀ b
    have d₁ := ratHeight_div_le a₁ b
    rw [← hx₀] at d₀
    rw [← hx₁] at d₁
    have hc := two_sq_canonHeightE_le (n i)
    have hP := two_canonHeight_genP0_gt_one
    have hB := heightB0_lt_ten
    have hsq : (n i : ℝ) ^ 2 ≤ 2 * (n i : ℝ) ^ 2 * canonHeightE genP0 := by
      nlinarith [sq_nonneg (n i : ℝ)]
    unfold heightB0 at hB
    linarith
  -- `N = max |nᵢ| ≥ 1` and `|f| ≤ 2 N²`
  set N : ℕ := max (max (n 0).natAbs (n 1).natAbs) (n 2).natAbs with hN
  have hle : ∀ i, (n i).natAbs ≤ N := by
    intro i; fin_cases i
    · exact le_trans (le_max_left _ _) (le_max_left _ _)
    · exact le_trans (le_max_right _ _) (le_max_left _ _)
    · exact le_max_right _ _
  have hN1 : 1 ≤ N := by
    by_contra h0
    have h0' : N = 0 := by omega
    have e0 : n 0 = 0 := Int.natAbs_eq_zero.mp (by have := hle 0; omega)
    have e2 : n 2 = 0 := Int.natAbs_eq_zero.mp (by have := hle 2; omega)
    exact hf (by rw [e0, e2]; ring)
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, (n i₀).natAbs = N := by
    rcases le_total (max (n 0).natAbs (n 1).natAbs) (n 2).natAbs with h | h
    · exact ⟨2, by rw [hN, max_eq_right h]⟩
    · rcases le_total (n 0).natAbs (n 1).natAbs with h' | h'
      · exact ⟨1, by rw [hN, max_eq_left h, max_eq_right h']⟩
      · exact ⟨0, by rw [hN, max_eq_left h, max_eq_left h']⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have habs : ∀ i, |(n i : ℝ)| ≤ N := fun i => by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast hle i
  have hfle : |((n 0 * n 1 - n 2 : ℤ) : ℝ)| ≤ 2 * (N : ℝ) ^ 2 := by
    push_cast
    calc |(n 0 : ℝ) * n 1 - n 2| ≤ |(n 0 : ℝ)| * |(n 1 : ℝ)| + |(n 2 : ℝ)| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ N * N + N := by
          gcongr
          · exact habs 0
          · exact habs 1
          · exact habs 2
      _ ≤ 2 * (N : ℝ) ^ 2 := by nlinarith
  -- `F ≤ 2 N^{48/25}`
  have hFle : F ≤ 2 * (N : ℝ) ^ ((48 : ℝ) / 25) := by
    have hN0 : (0 : ℝ) ≤ N := by positivity
    calc F ≤ (2 * (N : ℝ) ^ 2) ^ ((24 : ℝ) / 25) :=
          Real.rpow_le_rpow (abs_nonneg _) hfle (by norm_num)
      _ = (2 : ℝ) ^ ((24 : ℝ) / 25) * (N : ℝ) ^ ((48 : ℝ) / 25) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast (N : ℝ) 2,
            ← Real.rpow_mul hN0]
          norm_num
      _ ≤ 2 * (N : ℝ) ^ ((48 : ℝ) / 25) := by
          gcongr
          calc (2 : ℝ) ^ ((24 : ℝ) / 25) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  have hmain : (N : ℝ) ^ 2 < 24 * A * (N : ℝ) ^ ((48 : ℝ) / 25) + 10 := by
    have h1 := hidx i₀
    have h2 : (n i₀ : ℝ) ^ 2 = (N : ℝ) ^ 2 := by
      rw [← sq_abs, ← Int.cast_abs, Int.abs_eq_natAbs, hi₀]; push_cast; ring
    rw [h2] at h1
    nlinarith
  have hbox := box_inequality hA N hmain
  intro i
  exact lt_of_le_of_lt (habs i) hbox

/-- **The finite-box deduction**, from the data supplied by the height certificate: if
`n₁n₂ ≠ n₃` and for each `i` the coordinates of `x([nᵢ]P₀)` are `a_{ij}/bᵢ` with `bᵢ ≠ 0`, each of
the nine quantities `a_{ij}, bᵢ` being a sum of three slopes `t` with
`Slope(t, ℓ₀; c_*, c_*n₁, c_*n₂, c_*n₃)`, then `|nᵢ| < T` (given H). -/
theorem finite_box_of_slopes (hH : SixContactMin) (n : Fin 3 → ℤ)
    (hf : n 0 * n 1 ≠ n 2)
    (hcert : ∀ i, ∃ a₀ a₁ b : ℚ, b ≠ 0 ∧ b * iota (n i) 1 = a₀ ∧ b * iota (n i) 2 = a₁ ∧
      ∀ Q ∈ ({a₀, a₁, b} : Set ℚ), ∃ t₁ t₂ t₃ : ℚ, t₁ + t₂ + t₃ = Q ∧
        ∀ t ∈ ({t₁, t₂, t₃} : Set ℚ), SlopePred t (Syntax.ell : ℚ) (certShifts n)) :
    ∀ i, |n i| < (Syntax.T : ℤ) := by
  have hf' : n 0 * n 1 - n 2 ≠ 0 := sub_ne_zero.mpr hf
  have hA : (1 : ℝ) ≤ Syntax.Aht := by exact_mod_cast Syntax.Aht_pos
  have hb := finite_box_of_heights hA n hf' fun i => by
    obtain ⟨a₀, a₁, b, hb, e₀, e₁, hQ⟩ := hcert i
    refine ⟨a₀, a₁, b, hb, e₀, e₁, fun Q hQm => ?_⟩
    obtain ⟨t₁, t₂, t₃, hsum, hts⟩ := hQ Q hQm
    exact ⟨t₁, t₂, t₃, hsum, fun t ht => (slope_height_le hH n hf' (hts t ht)).2⟩
  intro i
  have := hb i
  have hT : ((Syntax.T : ℕ) : ℝ) = (48 * (Syntax.Aht : ℝ)) ^ 13 := by
    rw [Syntax.T_eq]; push_cast; ring
  rw [← hT] at this
  exact_mod_cast this

theorem nineQ_surj (A : Fin 3 → Fin 2 → ℚ) (b : Fin 3 → ℚ) (i : Fin 3) :
    (∃ k, nineQ A b k = A i 0) ∧ (∃ k, nineQ A b k = A i 1) ∧ ∃ k, nineQ A b k = b i := by
  fin_cases i
  · exact ⟨⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩⟩
  · exact ⟨⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩⟩
  · exact ⟨⟨6, rfl⟩, ⟨7, rfl⟩, ⟨8, rfl⟩⟩

/-- The finite-box deduction from the height-certificate predicate `HeightCert` at the codes
`ι(nᵢ)` with `ℓ = ℓ₀` and the shifts `(c_*, c_*n₁, c_*n₂, c_*n₃)`. -/
theorem finite_box_of_heightCert (hH : SixContactMin) (n : Fin 3 → ℤ)
    (hf : n 0 * n 1 ≠ n 2)
    (hcert : HeightCert (fun i => iota (n i)) (Syntax.ell : ℚ) (certShifts n)) :
    ∀ i, |n i| < (Syntax.T : ℤ) := by
  obtain ⟨A, b, hb, hQ⟩ := hcert
  refine finite_box_of_slopes hH n hf fun i => ?_
  obtain ⟨hb0, e₀, e₁⟩ := hb i
  refine ⟨A i 0, A i 1, b i, hb0, e₀, e₁, fun Q hQm => ?_⟩
  obtain ⟨⟨k₀, h₀⟩, ⟨k₁, h₁⟩, ⟨k₂, h₂⟩⟩ := nineQ_surj A b i
  have key : ∀ k, ∃ t₁ t₂ t₃ : ℚ, t₁ + t₂ + t₃ = nineQ A b k ∧
      ∀ t ∈ ({t₁, t₂, t₃} : Set ℚ), SlopePred t (Syntax.ell : ℚ) (certShifts n) := by
    intro k
    obtain ⟨u, hu, hs⟩ := hQ k
    refine ⟨u 0, u 1, u 2, hu, fun t ht => ?_⟩
    rcases ht with rfl | rfl | rfl
    exacts [hs 0, hs 1, hs 2]
  rcases hQm with rfl | rfl | rfl
  · rw [← h₀]; exact key k₀
  · rw [← h₁]; exact key k₁
  · rw [← h₂]; exact key k₂

/-- **The finite-box deduction** (Proposition 6.1). Assume the six-contact estimate.
If `n₁n₂ ≠ n₃` and the unguarded certificate accepts
`(ι(n₁), ι(n₂), ι(n₃), ℓ₀, ι(c_*), ι(c_*n₁), ι(c_*n₂), ι(c_*n₃))`, then `|nᵢ| < T`. The
parameter vector `a ∈ ℚ³⁶` of the height-certificate template is described coordinatewise. -/
theorem finite_box (hH : SixContactMin) (n : Fin 3 → ℤ)
    (hf : n 0 * n 1 ≠ n 2) (a : Fin 36 → ℚ)
    (hY : ∀ (i : Fin 3) (k : Fin 5), a ⟨5 * i + k, by omega⟩ = iota (n i) k)
    (hℓ : a 15 = (Syntax.ell : ℚ))
    (hc : ∀ (i : Fin 4) (k : Fin 5), a ⟨16 + (5 * i + k), by omega⟩ = iota (certShifts n i) k)
    (hacc : Syntax.heightTemplate.Rel a) :
    ∀ i, |n i| < (Syntax.T : ℤ) := by
  obtain ⟨-, hcert⟩ := (heightCertificate_rel_iff _ _ a hℓ hc).mp hacc
  have e : (fun (i : Fin 3) (k : Fin 5) => a ⟨5 * i + k, by omega⟩) = fun i => iota (n i) :=
    funext fun i => funext fun k => hY i k
  rw [e] at hcert
  exact finite_box_of_heightCert hH n hf hcert

end ZInQ.Mult
