import ZInQKernel.RouteK.Slots.Basic

/-!
# Route K, L6: points on `C_N` and `C_{Nθ}` give `PoleSoluble B`

`docs/research/rv-route-k.md` §4.2, with the rescalings of `docs/research/rv-slot-k-proof.md` §8.
Let `m` be a signed divisor of 2730, `β = sqf(mB)` and `θ = sqf(m(m − B))`, so that `A = mB = βt²`
and `H = A(A − B²) = B²·m(m − B) = θh²` with `h = Bc`. Given points `(βs², y₁)` on `C_N` and
`(βs'², y₂)` on `C_{Nθ}`:

* scaling the first point by `λ = t/s` gives `(A, λ³y₁)` on `C_e` with `e = Nλ²`;
* then `eH = Nθ μ²` with `μ = λh`, and scaling the second point by `μ` gives `(Az², μ³y₂)` on
  `C_{eH}` with `z = s'h/s`; the witness is `r₂ = μ³y₂/z`, since `(zr₂)² = z²T₂`;
* `w = (eHz)⁻¹`, and the bits `b` realize the multiplier `m` (`exists_multiplier_bits`).
-/

namespace ZInQ.RouteK

open scoped BigOperators

theorem gcd_prime_bit (k : ℕ) {p : ℕ} (hp : p.Prime) :
    ∃ c : ℚ, c ^ 2 - c = 0 ∧ ((Nat.gcd k p : ℕ) : ℚ) = 1 + ((p : ℚ) - 1) * c := by
  rcases hp.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right k p) with h | h
  · exact ⟨0, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨1, by norm_num, by rw [h]; ring⟩

/-- Every signed divisor `m` of 2730 is the multiplier `(1 − 2b₀)(1 + b₁)(1 + 2b₂)(1 + 4b₃)(1 + 6b₄)(1 + 12b₅)`
of the pole polynomial for some bits `b ∈ {0, 1}⁶`. -/
theorem exists_multiplier_bits {m : ℤ} (hm : m ∣ 2730) :
    ∃ b : Fin 6 → ℚ, (∀ i, b i ^ 2 - b i = 0) ∧
      (1 - 2 * b 0) * (1 + b 1) * (1 + 2 * b 2) * (1 + 4 * b 3) * (1 + 6 * b 4) *
        (1 + 12 * b 5) = m := by
  set k := m.natAbs with hkdef
  have hk : k ∣ 2730 := Int.natAbs_dvd_natAbs.mpr hm
  have hk' : k = Nat.gcd k 2 * Nat.gcd k 3 * Nat.gcd k 5 * Nat.gcd k 7 * Nat.gcd k 13 := by
    calc k = Nat.gcd k (2 * 3 * 5 * 7 * 13) := (Nat.gcd_eq_left hk).symm
      _ = _ := by
        rw [Nat.Coprime.gcd_mul k (by norm_num), Nat.Coprime.gcd_mul k (by norm_num),
          Nat.Coprime.gcd_mul k (by norm_num), Nat.Coprime.gcd_mul k (by norm_num)]
  obtain ⟨c₂, h₂, e₂⟩ := gcd_prime_bit k Nat.prime_two
  obtain ⟨c₃, h₃, e₃⟩ := gcd_prime_bit k Nat.prime_three
  obtain ⟨c₅, h₅, e₅⟩ := gcd_prime_bit k Nat.prime_five
  obtain ⟨c₇, h₇, e₇⟩ := gcd_prime_bit k (by norm_num : (7 : ℕ).Prime)
  obtain ⟨c₁₃, h₁₃, e₁₃⟩ := gcd_prime_bit k (by norm_num : (13 : ℕ).Prime)
  have hkq : (k : ℚ) = (1 + c₂) * (1 + 2 * c₃) * (1 + 4 * c₅) * (1 + 6 * c₇) * (1 + 12 * c₁₃) := by
    rw [hk']; push_cast; rw [e₂, e₃, e₅, e₇, e₁₃]; norm_num
  obtain ⟨c₀, h₀, e₀⟩ : ∃ c₀ : ℚ, c₀ ^ 2 - c₀ = 0 ∧ (m : ℚ) = (1 - 2 * c₀) * k := by
    rcases le_or_gt 0 m with h | h
    · refine ⟨0, by norm_num, ?_⟩
      rw [hkdef, Nat.cast_natAbs, abs_of_nonneg h]; ring
    · refine ⟨1, by norm_num, ?_⟩
      rw [hkdef, Nat.cast_natAbs, abs_of_neg h]; push_cast; ring
  refine ⟨![c₀, c₂, c₃, c₅, c₇, c₁₃], fun i => ?_, ?_⟩
  · fin_cases i <;> assumption
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    rw [e₀, hkq]; ring

/-- **L6**: if `C_N` and `C_{Nθ}` have rational points with nonzero abscissas in `βℚ*²`, where
`β = sqf(mB)`, `θ = sqf(m(m − B))` for a signed divisor `m ≠ B` of 2730, then the Route K pole
polynomial has a rational zero with input `B`. -/
theorem poleSoluble_of_points {B : ℚ} (hB : B ≠ 0) {m : ℤ} (hm : m ∣ 2730) (hmB : (m : ℚ) ≠ B)
    {N x₁ y₁ x₂ y₂ : ℚ} (hN : N ≠ 0)
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - N ^ 2 * x₁) (hx₁ : x₁ ≠ 0) (hs₁ : IsSquare (x₁ / betaOf B m))
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - (N * thetaOf B m) ^ 2 * x₂) (hx₂ : x₂ ≠ 0)
    (hs₂ : IsSquare (x₂ / betaOf B m)) : PoleSoluble B := by
  obtain ⟨b, hb, hbm⟩ := exists_multiplier_bits hm
  have hm0 : (m : ℚ) ≠ 0 := by
    intro h
    have : m = 0 := by exact_mod_cast h
    rw [this, zero_dvd_iff] at hm
    norm_num at hm
  obtain ⟨hβsq, t, ht, hAt⟩ := sqf_spec (mul_ne_zero hm0 hB)
  obtain ⟨hθsq, c, hc, hθc⟩ := sqf_spec (mul_ne_zero hm0 (sub_ne_zero.mpr hmB))
  change Squarefree (betaOf B m) at hβsq
  change (m : ℚ) * B = (betaOf B m : ℚ) * t ^ 2 at hAt
  change Squarefree (thetaOf B m) at hθsq
  change (m : ℚ) * (m - B) = (thetaOf B m : ℚ) * c ^ 2 at hθc
  set β : ℚ := (betaOf B m : ℚ) with hβdef
  set θ : ℚ := (thetaOf B m : ℚ) with hθdef
  have hβ0 : β ≠ 0 := by rw [hβdef]; exact_mod_cast hβsq.ne_zero
  have hθ0 : θ ≠ 0 := by rw [hθdef]; exact_mod_cast hθsq.ne_zero
  obtain ⟨s, hs⟩ := hs₁
  obtain ⟨s', hs'⟩ := hs₂
  have ex₁ : x₁ = β * s ^ 2 := by rw [div_eq_iff hβ0] at hs; rw [hs]; ring
  have ex₂ : x₂ = β * s' ^ 2 := by rw [div_eq_iff hβ0] at hs'; rw [hs']; ring
  have hs0 : s ≠ 0 := by rintro rfl; exact hx₁ (by rw [ex₁]; ring)
  have hs'0 : s' ≠ 0 := by rintro rfl; exact hx₂ (by rw [ex₂]; ring)
  subst ex₁ ex₂
  set h := B * c with hhdef
  have hh : h ≠ 0 := mul_ne_zero hB hc
  have hH : (m : ℚ) * B * ((m : ℚ) * B - B ^ 2) = θ * h ^ 2 := by
    rw [show (m : ℚ) * B * ((m : ℚ) * B - B ^ 2) = B ^ 2 * ((m : ℚ) * (m - B)) by ring, hθc]
    ring
  set e := N * (t / s) ^ 2 with hedef
  set z := s' * h / s with hzdef
  have he : e ≠ 0 := by positivity
  have hz : z ≠ 0 := by positivity
  have hw : e * (θ * h ^ 2) * z * (e * (θ * h ^ 2) * z)⁻¹ = 1 :=
    mul_inv_cancel₀ (by positivity)
  have hr₁ : (y₁ * (t / s) ^ 3) ^ 2 = β * t ^ 2 * (β * t ^ 2 - e) * (β * t ^ 2 + e) := by
    rw [hedef]
    linear_combination (norm := (field_simp; ring)) (t / s) ^ 6 * h₁
  have hr₂ : (y₂ * (t * h / s) ^ 3 / z) ^ 2 =
      β * t ^ 2 * (β * t ^ 2 * z ^ 2 - e * (θ * h ^ 2)) * (β * t ^ 2 * z ^ 2 + e * (θ * h ^ 2)) := by
    rw [hedef, hzdef]
    linear_combination (norm := (field_simp; ring)) ((t * h / s) ^ 6 / (s' * h / s) ^ 2) * h₂
  have hsum : ∑ i, (b i ^ 2 - b i) ^ 2 = 0 := Finset.sum_eq_zero fun i _ => by rw [hb i]; ring
  refine ⟨b, e, z, y₁ * (t / s) ^ 3, y₂ * (t * h / s) ^ 3 / z, (e * (θ * h ^ 2) * z)⁻¹, ?_⟩
  simp only [polePoly]
  rw [hbm, hH, hAt, hsum, hw, hr₁, hr₂]
  ring

end ZInQ.RouteK
