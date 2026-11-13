import ZInQKernel.Hypotheses.MordellWeil

/-!
# The field `K₀ = ℚ(√2)` and the ring `ℤ[√2]`

Blueprint: `model/field/quadratic-field.md`.

`K₀ = QuadraticAlgebra ℚ 2 0`, `s = sqrt2` and `d = genD` are defined in
`ZInQKernel/Hypotheses/MordellWeil.lean`. An element `⟨u, v⟩ : K₀` is `u + v s`; its
components are `re` and `im`, the conjugate is `star`, the norm is `QuadraticAlgebra.norm`
and the trace is `QuadraticAlgebra.trace`. Here we add the two real embeddings, total
positivity and sign vectors, the order `ℤ[s] = Zs`, and the elements `ε = 1 + s`, `δ = 3 - s`.
-/

namespace ZInQ

open QuadraticAlgebra

/-! ### Components and arithmetic in `K₀` -/

namespace K0

@[simp] theorem mk_re (u v : ℚ) : (⟨u, v⟩ : K0).re = u := rfl
@[simp] theorem mk_im (u v : ℚ) : (⟨u, v⟩ : K0).im = v := rfl

attribute [simp] QuadraticAlgebra.re_ofNat QuadraticAlgebra.im_ofNat QuadraticAlgebra.re_one
  QuadraticAlgebra.im_one

/-- Every element of `K₀` is `u + v s` with its components `u, v`. -/
theorem eq_re_add_im_mul_sqrt2 (z : K0) : z = (z.re : K0) + (z.im : K0) * sqrt2 := by
  ext <;> simp [sqrt2]

/-- The components determine an element of `K₀`. -/
theorem ext_iff' {z w : K0} : z = w ↔ z.re = w.re ∧ z.im = w.im :=
  QuadraticAlgebra.ext_iff

/-- The product rule `(a + b s)(c + e s) = (a c + 2 b e) + (a e + b c) s`. -/
theorem mk_mul_mk' (a b c e : ℚ) : (⟨a, b⟩ * ⟨c, e⟩ : K0) = ⟨a * c + 2 * b * e, a * e + b * c⟩ := by
  ext <;> simp

theorem norm_eq (z : K0) : QuadraticAlgebra.norm z = z.re ^ 2 - 2 * z.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]; ring

theorem star_eq' (z : K0) : star z = ⟨z.re, -z.im⟩ := by
  ext <;> simp

theorem trace_eq (z : K0) : QuadraticAlgebra.trace z = 2 * z.re := by
  rw [QuadraticAlgebra.trace_def]; ring

theorem mul_star_eq_norm (z : K0) : z * star z = algebraMap ℚ K0 (QuadraticAlgebra.norm z) :=
  (QuadraticAlgebra.algebraMap_norm_eq_mul_star z).symm

theorem norm_eq_zero_iff {z : K0} : QuadraticAlgebra.norm z = 0 ↔ z = 0 :=
  QuadraticAlgebra.norm_eq_zero_iff_eq_zero

end K0

theorem sqrt2_eq : sqrt2 = ⟨0, 1⟩ := rfl

theorem sqrt2_sq : sqrt2 ^ 2 = 2 := by
  ext <;> simp [sqrt2, pow_two]

theorem sqrt2_ne_zero : sqrt2 ≠ 0 := by
  intro h; have := congrArg QuadraticAlgebra.im h; simp [sqrt2] at this

theorem genD_eq : genD = 75 - 53 * sqrt2 := by
  ext <;> simp [genD, sqrt2]

/-! ### The real embeddings -/

theorem real_sqrt_two_mul_self : Real.sqrt 2 * Real.sqrt 2 = (2 : ℚ) • 1 + (0 : ℚ) • Real.sqrt 2 := by
  rw [Real.mul_self_sqrt (by norm_num)]; simp

theorem real_neg_sqrt_two_mul_self :
    (-Real.sqrt 2) * (-Real.sqrt 2) = (2 : ℚ) • 1 + (0 : ℚ) • (-Real.sqrt 2) := by
  rw [neg_mul_neg, Real.mul_self_sqrt (by norm_num)]; simp

namespace K0

/-- The real embedding `σ₊ : u + v s ↦ u + v √2`. -/
noncomputable def embPlus : K0 →+* ℝ :=
  (QuadraticAlgebra.lift ⟨Real.sqrt 2, real_sqrt_two_mul_self⟩).toRingHom

/-- The real embedding `σ₋ : u + v s ↦ u - v √2`. -/
noncomputable def embMinus : K0 →+* ℝ :=
  (QuadraticAlgebra.lift ⟨-Real.sqrt 2, real_neg_sqrt_two_mul_self⟩).toRingHom

theorem embPlus_apply (z : K0) : embPlus z = (z.re : ℝ) + z.im * Real.sqrt 2 := by
  simp [embPlus, Rat.smul_def]

theorem embMinus_apply (z : K0) : embMinus z = (z.re : ℝ) - z.im * Real.sqrt 2 := by
  simp [embMinus, Rat.smul_def, sub_eq_add_neg]

/-- `N(z) = σ₊(z) σ₋(z)`. -/
theorem norm_eq_embPlus_mul_embMinus (z : K0) :
    ((QuadraticAlgebra.norm z : ℚ) : ℝ) = embPlus z * embMinus z := by
  rw [embPlus_apply, embMinus_apply, norm_eq]
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  push_cast
  linear_combination (z.im : ℝ) ^ 2 * h

/-- `z` is totally positive if both real embeddings are positive. -/
def TotallyPositive (z : K0) : Prop := 0 < embPlus z ∧ 0 < embMinus z

/-- The sign vector of `z`: the pair of signs of `σ₊(z)` and `σ₋(z)`. -/
noncomputable def signVector (z : K0) : SignType × SignType :=
  (SignType.sign (embPlus z), SignType.sign (embMinus z))

theorem totallyPositive_iff_signVector {z : K0} :
    TotallyPositive z ↔ signVector z = (1, 1) := by
  simp [TotallyPositive, signVector, sign_eq_one_iff]

end K0

/-- `K₀` is a number field (of degree two). -/
instance : NumberField K0 where
  to_finiteDimensional := inferInstanceAs (Module.Finite ℚ (QuadraticAlgebra ℚ 2 0))

theorem finrank_K0 : Module.finrank ℚ K0 = 2 := QuadraticAlgebra.finrank_eq_two 2 0

/-! ### The elements `ε` and `δ` -/

/-- `ε = 1 + s`. -/
def epsilon : K0 := ⟨1, 1⟩

/-- `δ = 3 - s`. -/
def delta : K0 := ⟨3, -1⟩

theorem epsilon_eq : epsilon = 1 + sqrt2 := by
  ext <;> simp [epsilon, sqrt2]

theorem delta_eq : delta = 3 - sqrt2 := by
  ext <;> simp [delta, sqrt2]

/-! ### The order `ℤ[s]` -/

theorem not_isSquare_eight : ¬ IsSquare (8 : ℤ) := by
  rintro ⟨r, hr⟩
  have h1 : r.natAbs * r.natAbs = 8 := by
    have := congrArg Int.natAbs hr; simpa [Int.natAbs_mul] using this.symm
  have h2 : r.natAbs ≤ 3 := by nlinarith
  interval_cases r.natAbs <;> omega

instance : Fact (¬ IsSquare (QuadraticAlgebra.discr (2 : ℤ) 0)) :=
  ⟨by rw [QuadraticAlgebra.discr_def]; exact not_isSquare_eight⟩

/-- `ℤ[s] = ℤ[√2]`, an order of `K₀` (its ring of integers). -/
abbrev Zs : Type := QuadraticAlgebra ℤ 2 0

example : IsDomain Zs := inferInstance

/-- `ℤ[s] ⊆ K₀`. Mathlib's instance is stated for `QuadraticAlgebra ℚ ↑2 ↑0` (with integer
casts), which is `K₀` only up to unfolding the casts. -/
noncomputable instance : Algebra Zs K0 :=
  inferInstanceAs (Algebra (QuadraticAlgebra ℤ 2 0) (QuadraticAlgebra ℚ ((2 : ℤ) : ℚ) ((0 : ℤ) : ℚ)))

instance : IsFractionRing Zs K0 :=
  inferInstanceAs
    (IsFractionRing (QuadraticAlgebra ℤ 2 0) (QuadraticAlgebra ℚ ((2 : ℤ) : ℚ) ((0 : ℤ) : ℚ)))

/-- The inclusion `ℤ[s] → K₀`. -/
noncomputable abbrev Zs.toK0 : Zs →+* K0 := algebraMap Zs K0

@[simp] theorem Zs.toK0_re (z : Zs) : (Zs.toK0 z).re = z.re := rfl
@[simp] theorem Zs.toK0_im (z : Zs) : (Zs.toK0 z).im = z.im := rfl

theorem Zs.toK0_injective : Function.Injective Zs.toK0 :=
  IsFractionRing.injective Zs K0

theorem toK0_ne_zero {a : Zs} (ha : a ≠ 0) : Zs.toK0 a ≠ 0 :=
  (map_ne_zero_iff _ Zs.toK0_injective).mpr ha

theorem toK0_star (z : Zs) : Zs.toK0 (star z) = star (Zs.toK0 z) := by
  ext <;> simp

/-- `s` in `ℤ[s]`. -/
def sqrt2Z : Zs := ⟨0, 1⟩
/-- `d = 75 - 53 s` in `ℤ[s]`. -/
def genDZ : Zs := ⟨75, -53⟩
/-- `ε = 1 + s` in `ℤ[s]`. -/
def epsilonZ : Zs := ⟨1, 1⟩
/-- `δ = 3 - s` in `ℤ[s]`. -/
def deltaZ : Zs := ⟨3, -1⟩

@[simp] theorem toK0_sqrt2Z : Zs.toK0 sqrt2Z = sqrt2 := by ext <;> simp [sqrt2Z, sqrt2]
@[simp] theorem toK0_genDZ : Zs.toK0 genDZ = genD := by ext <;> simp [genDZ, genD]
@[simp] theorem toK0_epsilonZ : Zs.toK0 epsilonZ = epsilon := by ext <;> simp [epsilonZ, epsilon]
@[simp] theorem toK0_deltaZ : Zs.toK0 deltaZ = delta := by ext <;> simp [deltaZ, delta]

/-- `K₀` is the fraction field of `ℤ[s]`: every element is `a / b` with `a, b ∈ ℤ[s]`, `b ≠ 0`. -/
theorem exists_eq_div_Zs (z : K0) : ∃ a b : Zs, b ≠ 0 ∧ z = Zs.toK0 a / Zs.toK0 b := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Zs) z
  exact ⟨a, b, nonZeroDivisors.ne_zero hb, rfl⟩

end ZInQ
