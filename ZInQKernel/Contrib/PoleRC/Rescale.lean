import ZInQKernel.Contrib.PoleRC.Defs

/-!
# The rescaling to the eleven witnesses (`diophantine_zq.tex` lines 1107–1121)

* `point_of_locM`: a rational point in the class `(β, 1)` of `E_ℓ` (`ℓ > 0`, `β` not a square)
  has abscissa `β t²` with `t ≠ 0`.
* `polePoly_eq_zero_of`: the witnesses `b, e, z, r₁, r₂, w` with `bᵢ ∈ {0, 1}`, `(A, r₁) ∈ E_e`,
  `(Az², z r₂) ∈ E_{eH}` and `eHzw = 1` make `Q_pole` vanish.
* `poleSoluble_of_points`: the rescaling. From `A = β s²`, `H = θ c²` and points of `E_n`
  and `E_{nθ}` with abscissas in the square class of `β`, the eleven witnesses with
  `w = (eHz)⁻¹`.
-/

namespace ZInQ.Manuscript.PoleRC

/-- A rational point in the Kummer class `(β, 1)` of `E_ℓ`, for `ℓ > 0` and `β` not a square:
its abscissa is `β t²` with `t ≠ 0` (line 1111: "Their abscissas have squareclass `β`, by the cubic
equation"). -/
theorem point_of_locM {ℓ β : ℚ} (hℓ : 0 < ℓ) (hβ : ¬ IsSquare β) (h : LocM ℚ ℓ β 1) :
    ∃ t y : ℚ, t ≠ 0 ∧ y ^ 2 = (β * t ^ 2) * (β * t ^ 2 - ℓ) * (β * t ^ 2 + 3 * ℓ) := by
  rcases h with ⟨h1, -⟩ | ⟨x, ⟨u, hu⟩, ⟨v, hv⟩, ⟨t, ht⟩⟩
  · exact absurd h1 hβ
  have hβ0 : β ≠ 0 := by rintro rfl; exact hβ ⟨0, by ring⟩
  rw [div_one] at hv
  rw [mul_one] at ht
  have hx : x = β * (t * t) := by rw [← ht]; field_simp
  have hx3 : x + 3 * ℓ = β * (u * u) := by rw [← hu]; field_simp
  refine ⟨t, β * t * u * v, ?_, ?_⟩
  · rintro rfl
    have : x - ℓ < 0 := by rw [hx]; linarith
    nlinarith [mul_self_nonneg v]
  · rw [show β * t ^ 2 = x by rw [hx]; ring, hv, hx3, hx]; ring

/-- **`Q_pole` vanishes at the witnesses.** -/
theorem polePoly_eq_zero_of (B : ℚ) (b : Fin 6 → ℚ) (e z r₁ r₂ w : ℚ)
    (hb : ∀ i, b i = 0 ∨ b i = 1)
    (hA : ∀ A H : ℚ, A = (1 - 2 * b 0) * (1 + b 1) * (1 + 2 * b 2) * (1 + 4 * b 3) *
        (1 + 6 * b 4) * (1 + 12 * b 5) * B → H = A * (A - B ^ 2) →
        e * H * z * w = 1 ∧ r₁ ^ 2 = A * (A - e) * (A + 3 * e) ∧
        r₂ ^ 2 = A * (A * z ^ 2 - e * H) * (A * z ^ 2 + 3 * e * H)) :
    polePoly B b e z r₁ r₂ w = 0 := by
  obtain ⟨h1, h2, h3⟩ := hA _ _ rfl rfl
  have hb' : ∀ i, (b i ^ 2 - b i) ^ 2 = 0 := fun i => by
    rcases hb i with h | h <;> rw [h] <;> ring
  simp only [polePoly]
  rw [h1, h2, h3]
  simp [hb']

/-- **The rescaling** (lines 1111–1119). Let `A = β s²` and `H = θ c²` (`s, c ≠ 0`), `n ≠ 0`, and
let `(β t₁², y₁) ∈ E_n` and `(β t₂², y₂) ∈ E_{nθ}` with `t₁, t₂ ≠ 0`. With `q = t₁/s`,
`e = n/q²`, the first point divided by `q², q³` is `(A, r₁) ∈ E_e`; the second, rescaled to
`E_{nH}` by `c², c³` and divided by `q², q³`, is `(Az², z r₂) ∈ E_{eH}`; and `w = (eHz)⁻¹`. -/
theorem witnesses_of_points {A H β θ s c n t₁ y₁ t₂ y₂ : ℚ} (hs : s ≠ 0) (hc : c ≠ 0)
    (hn : n ≠ 0) (hθ : θ ≠ 0) (hβ : β ≠ 0) (hA : A = β * s ^ 2) (hH : H = θ * c ^ 2)
    (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0)
    (h₁ : y₁ ^ 2 = (β * t₁ ^ 2) * (β * t₁ ^ 2 - n) * (β * t₁ ^ 2 + 3 * n))
    (h₂ : y₂ ^ 2 = (β * t₂ ^ 2) * (β * t₂ ^ 2 - n * θ) * (β * t₂ ^ 2 + 3 * (n * θ))) :
    ∃ e z r₁ r₂ w : ℚ, e * H * z * w = 1 ∧ r₁ ^ 2 = A * (A - e) * (A + 3 * e) ∧
        r₂ ^ 2 = A * (A * z ^ 2 - e * H) * (A * z ^ 2 + 3 * e * H) := by
  set q := t₁ / s with hq
  have hq0 : q ≠ 0 := div_ne_zero ht₁ hs
  set z := c * t₂ / (s * q) with hz
  have hz0 : z ≠ 0 := div_ne_zero (mul_ne_zero hc ht₂) (mul_ne_zero hs hq0)
  have hH0 : H ≠ 0 := by rw [hH]; exact mul_ne_zero hθ (pow_ne_zero 2 hc)
  have he0 : n / q ^ 2 ≠ 0 := div_ne_zero hn (pow_ne_zero 2 hq0)
  refine ⟨n / q ^ 2, z, y₁ / q ^ 3, c ^ 3 * y₂ / (q ^ 3 * z), (n / q ^ 2 * H * z)⁻¹, ?_, ?_, ?_⟩
  · field_simp
  · have hAq : A = β * t₁ ^ 2 / q ^ 2 := by rw [hA, hq]; field_simp
    rw [div_pow, h₁, hAq]; field_simp
  · have hAz : A * z ^ 2 = c ^ 2 * (β * t₂ ^ 2) / q ^ 2 := by rw [hA, hz]; field_simp
    have hAq : A = c ^ 2 * (β * t₂ ^ 2) / (q ^ 2 * z ^ 2) := by
      rw [div_mul_eq_div_div, ← hAz]; field_simp
    rw [div_pow, mul_pow, h₂, hAz]
    conv_rhs => rw [hAq]
    rw [hH]; field_simp

end ZInQ.Manuscript.PoleRC
