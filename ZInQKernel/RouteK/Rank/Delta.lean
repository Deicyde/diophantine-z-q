import ZInQKernel.RouteK.Rank.KummerAt
import ZInQKernel.RouteK.Selmer.Covering

/-!
# The complete 2-descent map on `C_d : y² = x³ − d²x`

Over a field `K` with `2 ≠ 0` and `d ≠ 0`, the curve `C_d` is `shortCurve (−d²)` and the roots of
`x³ − d²x` are `0, d, −d`. The complete 2-descent map (Silverman X.1.4) is

`δ_d : C_d(K) → K*/K*² × K*/K*²`, `P ↦ (kummerAt (−d²) 0 P, kummerAt (−d²) d P)`,

i.e. `(x, y) ↦ (x, x − d)` with the values `(−d², −d) ≡ (−1, −d)` at `(0, 0)`, `(d, 2d²) ≡ (d, 2)`
at `(d, 0)` and `(−d, −2d)` at `(−d, 0)`. It is a homomorphism (`deltaHom`), it agrees with the
Kummer map `Selmer.kummer` of `Covering.lean` read in square classes (`delta_eq_sqc_kummer`), and
it kills `2 C_d(K)`. Conversely (`exists_two_nsmul_eq_of_squares`, the halving lemma): if `x`,
`x − d`, `x + d` are squares then `(x, y)` is twice a `K`-point; the half is given by the explicit
formula `x' = x + r₁r₂ + r₁r₃ + r₂r₃`, `y' = (r₁ + r₂)(r₁ + r₃)(r₂ + r₃)` for `x = r₁²`,
`x − d = r₂²`, `x + d = r₃²`.
-/

namespace ZInQ.RouteK.Rank

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Descent

variable {K : Type*} [Field K] [DecidableEq K]

/-- The complete 2-descent map of `C_d`: `P ↦ (kummerAt (−d²) 0 P, kummerAt (−d²) d P)`. -/
noncomputable def delta (d : K) (P : (shortCurve (-d ^ 2)).toAffine.Point) :
    SqClass K × SqClass K :=
  (kummerAt (-d ^ 2) 0 P, kummerAt (-d ^ 2) d P)

omit [DecidableEq K] in
theorem delta_root_zero (d : K) : (0 : K) ^ 3 + -d ^ 2 * 0 = 0 := by ring

omit [DecidableEq K] in
theorem delta_root_d (d : K) : d ^ 3 + -d ^ 2 * d = 0 := by ring

variable {d : K}

omit [DecidableEq K] in
theorem delta_b_ne_zero (hd : d ≠ 0) : -d ^ 2 ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 hd)

variable (h2 : (2 : K) ≠ 0) (hd : d ≠ 0)
include h2 hd

/-- The complete 2-descent map is a homomorphism. -/
theorem delta_add (P Q : (shortCurve (-d ^ 2)).toAffine.Point) :
    delta d (P + Q) = delta d P * delta d Q := by
  simp only [delta, kummerAt_add h2 (delta_b_ne_zero hd) (delta_root_zero d),
    kummerAt_add h2 (delta_b_ne_zero hd) (delta_root_d d), Prod.mk_mul_mk]

/-- The complete 2-descent map as a homomorphism to `Additive ((K*/K*²)²)`. -/
noncomputable def deltaHom :
    (shortCurve (-d ^ 2)).toAffine.Point →+ Additive (SqClass K × SqClass K) where
  toFun P := Additive.ofMul (delta d P)
  map_zero' := rfl
  map_add' P Q := by rw [delta_add h2 hd]; rfl

@[simp] theorem deltaHom_apply (P : (shortCurve (-d ^ 2)).toAffine.Point) :
    Additive.toMul (deltaHom h2 hd P) = delta d P := rfl

/-- `δ_d` read through `Selmer.kummer`: `δ_d(P) = (sqc k₁, sqc k₂)` for `(k₁, k₂) = kummer d P`. -/
theorem delta_eq_sqc_kummer (P : (shortCurve (-d ^ 2)).toAffine.Point) :
    delta d P = (sqc (Selmer.kummer d P).1, sqc (Selmer.kummer d P).2) := by
  have hd2 : d ≠ -d := fun h => mul_ne_zero h2 hd (by linear_combination h)
  rcases P with _ | ⟨x, y, h⟩
  · simp [delta, Selmer.kummer, show (Point.zero : (shortCurve (-d ^ 2)).toAffine.Point) = 0
      from rfl]
  simp only [delta, Selmer.kummer, kummerAt_some]
  by_cases hx0 : x = 0
  · subst hx0
    simp only [↓reduceIte, hd.symm, zero_sub, Prod.mk.injEq]
    refine ⟨?_, trivial⟩
    rw [show (3 : K) * 0 ^ 2 + -d ^ 2 = -1 * d ^ 2 by ring, sqc_mul_sq _ hd]
  by_cases hx1 : x = d
  · subst hx1
    simp only [hx0, ↓reduceIte, sub_zero, Prod.mk.injEq, true_and]
    rw [show (3 : K) * x ^ 2 + -x ^ 2 = 2 * x ^ 2 by ring, sqc_mul_sq _ hd]
  by_cases hx2 : x = -d
  · subst hx2
    simp only [hx0, hx1, ↓reduceIte, sub_zero, Prod.mk.injEq, true_and]
    congr 1; ring
  simp [hx0, hx1, hx2]

/-- `δ_d` kills `2 C_d(K)`. -/
theorem delta_two_nsmul (P : (shortCurve (-d ^ 2)).toAffine.Point) : delta d (2 • P) = 1 := by
  rw [two_nsmul, delta_add h2 hd]
  ext <;> simp [SqClass.mul_self]

omit [DecidableEq K] h2 hd in
/-- The halving formula, as polynomial identities. -/
theorem halve_identities (r₁ r₂ r₃ : K) (h3 : r₁ ^ 2 + (r₁ ^ 2 - r₂ ^ 2) = r₃ ^ 2) :
    ((r₁ + r₂) * (r₁ + r₃) * (r₂ + r₃)) ^ 2 =
        (r₁ ^ 2 + r₁ * r₂ + r₁ * r₃ + r₂ * r₃) ^ 3 +
          -(r₁ ^ 2 - r₂ ^ 2) ^ 2 * (r₁ ^ 2 + r₁ * r₂ + r₁ * r₃ + r₂ * r₃) ∧
      (3 * (r₁ ^ 2 + r₁ * r₂ + r₁ * r₃ + r₂ * r₃) ^ 2 + -(r₁ ^ 2 - r₂ ^ 2) ^ 2) ^ 2 =
        (r₁ ^ 2 + 2 * (r₁ ^ 2 + r₁ * r₂ + r₁ * r₃ + r₂ * r₃)) *
          (2 * ((r₁ + r₂) * (r₁ + r₃) * (r₂ + r₃))) ^ 2 := by
  constructor
  · linear_combination (-(r₁ ^ 3 * r₂ + 2 * r₁ ^ 2 * r₂ ^ 2 + r₁ * r₂ ^ 3 +
      r₃ ^ 2 * (r₁ ^ 2 + 2 * r₁ * r₂ + r₂ ^ 2) +
      r₃ * (r₁ ^ 3 + 3 * r₁ ^ 2 * r₂ + 3 * r₁ * r₂ ^ 2 + r₂ ^ 3))) * h3
  · linear_combination (-(-2 * r₁ ^ 6 - 12 * r₁ ^ 5 * r₂ - 23 * r₁ ^ 4 * r₂ ^ 2 -
      20 * r₁ ^ 3 * r₂ ^ 3 - 8 * r₁ ^ 2 * r₂ ^ 4 + r₂ ^ 6 +
      r₃ ^ 3 * (-8 * r₁ ^ 3 - 24 * r₁ ^ 2 * r₂ - 24 * r₁ * r₂ ^ 2 - 8 * r₂ ^ 3) +
      r₃ ^ 2 * (-19 * r₁ ^ 4 - 60 * r₁ ^ 3 * r₂ - 70 * r₁ ^ 2 * r₂ ^ 2 - 36 * r₁ * r₂ ^ 3 -
        7 * r₂ ^ 4) +
      r₃ * (-12 * r₁ ^ 5 - 48 * r₁ ^ 4 * r₂ - 72 * r₁ ^ 3 * r₂ ^ 2 - 48 * r₁ ^ 2 * r₂ ^ 3 -
        12 * r₁ * r₂ ^ 4))) * h3

omit [DecidableEq K] h2 hd in
/-- Two points of `C_d` with the same abscissa are equal or opposite. -/
theorem some_eq_or_eq_neg {x y X Y : K} (h : (shortCurve (-d ^ 2)).toAffine.Nonsingular x y)
    (h' : (shortCurve (-d ^ 2)).toAffine.Nonsingular X Y) (hX : X = x) :
    Point.some x y h = .some X Y h' ∨ Point.some x y h = -Point.some X Y h' := by
  have e₁ := (shortCurve_equation_iff _ x y).mp h.1
  have e₂ := (shortCurve_equation_iff _ X Y).mp h'.1
  subst hX
  have : (y - Y) * (y + Y) = 0 := by linear_combination e₁ - e₂
  rcases mul_eq_zero.mp this with h0 | h0
  · left; simp only [Point.some.injEq, true_and]; linear_combination h0
  · right; simp only [Point.neg_some, Point.some.injEq, shortCurve_negY, true_and]
    linear_combination h0

/-- **The halving lemma.** If `x = r₁²`, `x − d = r₂²` and `x + d = r₃²`, then `(x, y) ∈ C_d(K)` is
twice a `K`-point. -/
theorem exists_two_nsmul_eq_of_squares {x y : K} (h : (shortCurve (-d ^ 2)).toAffine.Nonsingular x y)
    {r₁ r₂ r₃ : K} (h₁ : x = r₁ ^ 2) (h₂ : x - d = r₂ ^ 2) (h₃ : x + d = r₃ ^ 2) :
    ∃ Q : (shortCurve (-d ^ 2)).toAffine.Point, 2 • Q = .some x y h := by
  have : NeZero (2 : K) := ⟨h2⟩
  have : (shortCurve (-d ^ 2)).IsElliptic := shortCurve_isElliptic (delta_b_ne_zero hd)
  subst h₁
  have hdr : d = r₁ ^ 2 - r₂ ^ 2 := by linear_combination -h₂
  have h3 : r₁ ^ 2 + (r₁ ^ 2 - r₂ ^ 2) = r₃ ^ 2 := by rw [← hdr]; exact h₃
  obtain ⟨heq, hdbl⟩ := halve_identities r₁ r₂ r₃ h3
  set x' := r₁ ^ 2 + r₁ * r₂ + r₁ * r₃ + r₂ * r₃ with hx'
  set y' := (r₁ + r₂) * (r₁ + r₃) * (r₂ + r₃) with hy'
  have hQ : (shortCurve (-d ^ 2)).toAffine.Equation x' y' := by
    rw [shortCurve_equation_iff, hdr]; exact heq
  -- `y' ≠ 0`: `r_i + r_j = 0` would make two of `x, x − d, x + d` equal
  have hy0 : y' ≠ 0 := by
    have h12 : r₁ + r₂ ≠ 0 := by
      intro h0; apply hd; rw [hdr, show r₁ = -r₂ by linear_combination h0]; ring
    have h13 : r₁ + r₃ ≠ 0 := by
      intro h0; apply hd
      linear_combination h₃ - (r₁ - r₃) * h0
    have h23 : r₂ + r₃ ≠ 0 := by
      intro h0
      apply mul_ne_zero h2 hd
      linear_combination h₃ - h₂ + (r₃ - r₂) * h0
    exact mul_ne_zero (mul_ne_zero h12 h13) h23
  have hyn : y' ≠ (shortCurve (-d ^ 2)).toAffine.negY x' y' := by
    rw [shortCurve_negY]; intro h0; apply hy0
    have : (2 : K) * y' = 0 := by linear_combination h0
    exact (mul_eq_zero.mp this).resolve_left h2
  have hyy : y' - -y' ≠ 0 := by
    intro h0; apply hy0
    have : (2 : K) * y' = 0 := by linear_combination h0
    exact (mul_eq_zero.mp this).resolve_left h2
  set Q : (shortCurve (-d ^ 2)).toAffine.Point := Point.mk hQ
  have hX : (shortCurve (-d ^ 2)).toAffine.addX x' x'
      ((shortCurve (-d ^ 2)).toAffine.slope x' x' y' y') = r₁ ^ 2 := by
    rw [Affine.slope_of_Y_ne rfl hyn]
    simp only [Affine.addX, shortCurve_negY, shortCurve_a₁, shortCurve_a₂, shortCurve_a₄,
      mul_zero, zero_mul, add_zero, sub_zero]
    rw [div_pow, hdr, sub_sub, sub_eq_iff_eq_add, div_eq_iff (pow_ne_zero 2 hyy)]
    linear_combination hdbl
  have h2Q : 2 • Q = Point.some _ _ (nonsingular_add (equation_iff_nonsingular.mp hQ)
      (equation_iff_nonsingular.mp hQ) fun hxy => hyn hxy.right) := by
    rw [two_nsmul]; exact Point.add_self_of_Y_ne hyn
  rcases some_eq_or_eq_neg h _ hX with e | e
  · exact ⟨Q, by rw [h2Q, e]⟩
  · exact ⟨-Q, by rw [smul_neg, h2Q, e]⟩

end ZInQ.RouteK.Rank
