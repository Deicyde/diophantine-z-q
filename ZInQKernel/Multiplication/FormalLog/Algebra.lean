import Mathlib

/-!
# The chord algebra behind the formal group law of `y² = x³ + A x`

In the coordinates `z = -x/y`, `ω = -1/y` the curve is `ω = z³ + A z ω²`. Let two points
`(a, ω₁)`, `(b, ω₂)` lie on the line `ω = λ z + ν`. Substituting the line into the curve gives
the cubic `c(z) = (1 + Aλ²) z³ + 2Aλν z² + (Aν² - λ) z - ν`, which vanishes at `a` and `b`.

* `chordQ_of_roots`: dividing `c(a) - c(b)` by `a - b` gives the relation `Q = 0`;
* `chord_third_root`: the third root of `c` is `-F` with `F = a + b + 2Aλν/(1 + Aλ²)`, so
  `(F, λF - ν)` satisfies `W = F³ + A F W²` (`W = λF - ν` is minus the third `ω`);
* `chord_slope_deriv`, `chord_invariance`: if `λ`, `ν`, `ω₁` depend on `a` (with derivatives
  `m = ∂λ`, `d = ∂ω₁`, `J = ∂(1 + Aλ²)⁻¹`), then
  `∂F · (1 - 2A a ω₁) = 1 - 2A F W`: the invariant differential `dz/(1 - 2Azω)` is invariant
  under the chord addition.

These are identities in an arbitrary commutative ring (a domain where we cancel `a - b`), used
in `K⟦T₁, T₂⟧` with `a = T₁`, `b = T₂`. The certificates were found with a computer algebra
system.
-/

namespace ZInQ.Mult

variable {R : Type*} [CommRing R]

/-- `c(a) = c(b) = 0` and `a ≠ b` give `Q = 0`, where `(a - b) Q = c(a) - c(b)`. -/
theorem chordQ_of_roots [NoZeroDivisors R] {A a b l n : R} (hab : a - b ≠ 0)
    (ha : l * a + n = a ^ 3 + A * a * (l * a + n) ^ 2)
    (hb : l * b + n = b ^ 3 + A * b * (l * b + n) ^ 2) :
    (1 + A * l ^ 2) * (a ^ 2 + a * b + b ^ 2) + 2 * A * l * n * (a + b) + A * n ^ 2 - l = 0 := by
  have h : (a - b) * ((1 + A * l ^ 2) * (a ^ 2 + a * b + b ^ 2) + 2 * A * l * n * (a + b) +
      A * n ^ 2 - l) = 0 := by
    linear_combination hb - ha
  exact (mul_eq_zero.mp h).resolve_left hab

/-- The third intersection: `W = λF - ν` satisfies `W = F³ + A F W²`. -/
theorem chord_third_root {A a b l n I F : R}
    (ha : l * a + n = a ^ 3 + A * a * (l * a + n) ^ 2)
    (hQ : (1 + A * l ^ 2) * (a ^ 2 + a * b + b ^ 2) + 2 * A * l * n * (a + b) + A * n ^ 2 - l = 0)
    (he : I * (1 + A * l ^ 2) = 1) (hF : F = a + b + 2 * A * l * n * I) :
    l * F - n = F ^ 3 + A * F * (l * F - n) ^ 2 := by
  subst hF
  linear_combination (-1 : R) * ha +
    (-2 * A * l * n * ((a + b + 2 * A * l * n * I) ^ 2 - a ^ 2) +
      2 * A * l * n * (a + b) * (-(a + b + 2 * A * l * n * I) - a)) * he +
    (-(a + b + 2 * A * l * n * I) - a) * hQ

/-- The derivative of the slope: `m (1 - 2A a ω₁) = (1 + Aλ²)(2a + b) + 2Aλν`. -/
theorem chord_slope_deriv [NoZeroDivisors R] {A a b l n m d : R} (hab : a - b ≠ 0)
    (hQ : (1 + A * l ^ 2) * (a ^ 2 + a * b + b ^ 2) + 2 * A * l * n * (a + b) + A * n ^ 2 - l = 0)
    (hd : m * (b - a) = l - d)
    (h5 : d * (1 - 2 * A * a * (l * a + n)) = 3 * a ^ 2 + A * (l * a + n) ^ 2) :
    m * (1 - 2 * A * a * (l * a + n)) = (1 + A * l ^ 2) * (2 * a + b) + 2 * A * l * n := by
  have h : (a - b) * ((1 + A * l ^ 2) * (2 * a + b) + 2 * A * l * n -
      m * (1 - 2 * A * a * (l * a + n))) = 0 := by
    linear_combination (1 - 2 * A * a * (l * a + n)) * hd - h5 - hQ
  exact (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hab)).symm

/-- **Invariance of the differential** under the chord addition:
`∂F · (1 - 2A a ω₁) = 1 - 2A F (λF - ν)`. -/
theorem chord_invariance {A a b l n I m d J dn F dF : R}
    (he : I * (1 + A * l ^ 2) = 1) (hJ : J = -(2 * A * l * m * I ^ 2)) (hd : d = l - m * (b - a))
    (h7 : m * (1 - 2 * A * a * (l * a + n)) = (1 + A * l ^ 2) * (2 * a + b) + 2 * A * l * n)
    (hdn : dn = d - m * a - l) (hF : F = a + b + 2 * A * l * n * I)
    (hdF : dF = 1 + 2 * A * (m * n * I + l * dn * I + l * n * J)) :
    dF * (1 - 2 * A * a * (l * a + n)) = 1 - 2 * A * F * (l * F - n) := by
  subst hF hdF hdn
  linear_combination (-2 * A * l * n * (2 * A * a ^ 2 * l + 2 * A * a * n - 1)) * hJ +
    (-2 * A * I * l * (2 * A * a ^ 2 * l + 2 * A * a * n - 1)) * hd +
    (-2 * A * I * (2 * A * I * l ^ 2 * n + b * l - n)) * h7 +
    (-2 * A * (2 * a + b) * (2 * A * I * l ^ 2 * n + b * l - n)) * he

end ZInQ.Mult
