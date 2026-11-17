import Mathlib

/-!
# Lane RC15 (central): the Euler-factor identities of Lemma `ex:arith-common-coordinate`

The exact algebra behind (4.7) in the 11/5 manuscript (`diophantine_zq.tex`, Lemma
`ex:arith-common-coordinate`, lines 4142–4317), and the moving-prime identity used in the
calibration (4.6) (Proposition `ex:arith-central-calibration`, lines 4066–4078).

All statements are over an arbitrary commutative ring `R` (in the manuscript `R = 𝒪[G]`,
`𝒪 = (ℤ₂[[t]]_{(2)})^`, `G` a finite elementary abelian two-group), with the Frobenius at the unused
prime `q` an actual `2 × 2` matrix `F` with `tr F = a_q`, `det F = q`, a scalar Frobenius value
`z` with inverse `zi = z⁻¹`, and `qi = q⁻¹` (the manuscript inverts `q` only after the inner limit
and localization at `(2)`, tex 4282–4284; here `qi` is a hypothesis-carried inverse).

Every declaration in this file is `PROVED`.

* `det_smul_sub_smul_one`, `det_one_sub_smul`: the two characteristic-polynomial evaluations.
* `quotientDet_eq` (tex 4183–4184): `δ_q = det(z Fr_q − q) det(z⁻¹ Fr_q − q) = q⁴ l_q`.
* `sq_mul_quotientFactor` (tex 4214–4215): `q² l_q = e_q² + (q − 1)(q − 1 − (z + z⁻¹) e_q)`.
* `sq_mul_quotientFactor_expanded` (tex 4279–4280): `q² l_q = (q−1)² + a_q² − a_q(q+1)s_q + q s_q²`.
* `quotientFactor_mul_inv_sq` (tex 4216–4218, 4279–4282): for odd `q = 1 + 2m` and a unit
  `e_q`, `l_q / e_q² = 1 + 2 v_q` with the manuscript's
  `v_q = (q−1)/(2q²e_q²)·(−(q+1)e_q² + (q−1) − s_q e_q)`; so `l_q/e_q² − 1 ∈ 2R`.
* `pointFactor_swap`, `quotientFactor_swap` (tex 4170–4171, 4271–4272): conjugation and
  orientation reversal `z ↦ z⁻¹` leave `e_q` and `l_q` unchanged.
* `residue_pointFactor`, `residue_quotientFactor`, `residue_pointFactor_ne_zero`
  (tex 4197–4205, 4284–4288): modulo `(2, I_G)`, `ē_q = t²/(1+t) ≠ 0` and `l̄_q = t⁴/(1+t)²`.
* `isUnit_pointFactor` (tex 4205): in a local ring whose maximal ideal the reduction kills,
  `e_q` is a unit.
* `movingNorm_eq`, `padicValInt_movingNorm` (tex 4066–4074): `N_i = (r_i − 1) − χ_h(r_i) m_i`, and
  `v₂ N_i = v₂ m_i` when `2^{B_i} ∣ r_i − 1` and `v₂ m_i < B_i`.
-/

namespace ZInQ.Manuscript.RC.Central

open Matrix

section EulerFactors

variable {R : Type*} [CommRing R]

/-- The point factor `e_q = a_q − z − z⁻¹` at an unused good split prime `q`
(tex 4151, 4166), with `zi = z⁻¹`. -/
def pointFactor (a z zi : R) : R := a - z - zi

/-- The two-place quotient factor `l_q = det(1 − q⁻¹ z Fr_q) · det(1 − q⁻¹ z⁻¹ Fr_q)`
(tex 4208–4210), with `F` the Frobenius matrix, `qi = q⁻¹` and `zi = z⁻¹`. -/
def quotientFactor (F : Matrix (Fin 2) (Fin 2) R) (qi z zi : R) : R :=
  (1 - (qi * z) • F).det * (1 - (qi * zi) • F).det

/-- The two quotient determinants `δ_q = det(z Fr_q − q) · det(z⁻¹ Fr_q − q)` (tex 4183–4184). -/
def quotientDet (F : Matrix (Fin 2) (Fin 2) R) (q z zi : R) : R :=
  (z • F - q • (1 : Matrix (Fin 2) (Fin 2) R)).det * (zi • F - q • (1 : Matrix (Fin 2) (Fin 2) R)).det

/-- `det(x F − y) = x² det F − x y tr F + y²` for a `2 × 2` matrix. PROVED. -/
theorem det_smul_sub_smul_one (F : Matrix (Fin 2) (Fin 2) R) (x y : R) :
    (x • F - y • (1 : Matrix (Fin 2) (Fin 2) R)).det = x ^ 2 * F.det - x * y * F.trace + y ^ 2 := by
  simp [det_fin_two, trace_fin_two, Matrix.sub_apply, Matrix.smul_apply]
  ring

/-- `det(1 − x F) = 1 − x tr F + x² det F` for a `2 × 2` matrix. PROVED. -/
theorem det_one_sub_smul (F : Matrix (Fin 2) (Fin 2) R) (x : R) :
    (1 - x • F).det = 1 - x * F.trace + x ^ 2 * F.det := by
  simp [det_fin_two, trace_fin_two, Matrix.sub_apply, Matrix.smul_apply]
  ring

/-- `q · det(1 − q⁻¹ z F) = q − z tr F + z²` when `det F = q`. PROVED. -/
theorem mul_det_one_sub_smul {F : Matrix (Fin 2) (Fin 2) R} {q qi a : R} (z : R)
    (hq : q * qi = 1) (ha : F.trace = a) (hd : F.det = q) :
    q * (1 - (qi * z) • F).det = q - z * a + z ^ 2 := by
  rw [det_one_sub_smul, ha, hd]
  linear_combination (-(z * a) + z ^ 2 * q * qi + z ^ 2) * hq

/-- **`δ_q = q⁴ l_q`** (tex 4183–4184): the two quotient determinants are `q⁴` times the
two-place quotient factor, for a Frobenius matrix with trace `a_q` and determinant `q`. PROVED. -/
theorem quotientDet_eq {F : Matrix (Fin 2) (Fin 2) R} {q qi a : R} (z zi : R)
    (hq : q * qi = 1) (ha : F.trace = a) (hd : F.det = q) :
    quotientDet F q z zi = q ^ 4 * quotientFactor F qi z zi := by
  have h1 := mul_det_one_sub_smul z hq ha hd
  have h2 := mul_det_one_sub_smul zi hq ha hd
  unfold quotientDet quotientFactor
  rw [det_smul_sub_smul_one, det_smul_sub_smul_one, ha, hd]
  have : q ^ 4 * ((1 - (qi * z) • F).det * (1 - (qi * zi) • F).det) =
      (q * (q * (1 - (qi * z) • F).det)) * (q * (q * (1 - (qi * zi) • F).det)) := by ring
  rw [this, h1, h2]
  ring

/-- `q² l_q = (q − z a_q + z²)(q − z⁻¹ a_q + z⁻²)`. PROVED. -/
theorem sq_mul_quotientFactor_prod {F : Matrix (Fin 2) (Fin 2) R} {q qi a : R} (z zi : R)
    (hq : q * qi = 1) (ha : F.trace = a) (hd : F.det = q) :
    q ^ 2 * quotientFactor F qi z zi = (q - z * a + z ^ 2) * (q - zi * a + zi ^ 2) := by
  rw [← mul_det_one_sub_smul z hq ha hd, ← mul_det_one_sub_smul zi hq ha hd]
  unfold quotientFactor; ring

/-- **The exact identity `q² l_q = e_q² + (q − 1)(q − 1 − (z + z⁻¹) e_q)`** (tex 4211–4215),
obtained by expanding the two degree-two polynomials, for `z z⁻¹ = 1`. PROVED. -/
theorem sq_mul_quotientFactor {F : Matrix (Fin 2) (Fin 2) R} {q qi a z zi : R}
    (hq : q * qi = 1) (hz : z * zi = 1) (ha : F.trace = a) (hd : F.det = q) :
    q ^ 2 * quotientFactor F qi z zi =
      pointFactor a z zi ^ 2 + (q - 1) * (q - 1 - (z + zi) * pointFactor a z zi) := by
  rw [sq_mul_quotientFactor_prod z zi hq ha hd]
  unfold pointFactor
  linear_combination (a ^ 2 - a * (z + zi) + z * zi + 1 - 2 * q) * hz

/-- **The expanded form** `q² l_q = (q − 1)² + a_q² − a_q (q + 1) s_q + q s_q²`, `s_q = z + z⁻¹`
(tex 4278–4280). PROVED. -/
theorem sq_mul_quotientFactor_expanded {F : Matrix (Fin 2) (Fin 2) R} {q qi a z zi : R}
    (hq : q * qi = 1) (hz : z * zi = 1) (ha : F.trace = a) (hd : F.det = q) :
    q ^ 2 * quotientFactor F qi z zi =
      (q - 1) ^ 2 + a ^ 2 - a * (q + 1) * (z + zi) + q * (z + zi) ^ 2 := by
  rw [sq_mul_quotientFactor hq hz ha hd]
  unfold pointFactor
  ring

/-- **Integrality of the correction** (tex 4216–4219, 4278–4283): for odd `q = 1 + 2m` with
inverse `qi` and a point factor `e_q` with inverse `ei`, `l_q / e_q² = 1 + 2 v_q` with
`v_q = m (−(q+1) e_q² + (q − 1) − s_q e_q) q⁻² e_q⁻²`, which is the manuscript's
`v_q = (q−1)/(2q²e_q²)·(−(q+1)e_q² + (q−1) − s_q e_q)` (here `(q − 1)/2 = m`). Hence
`l_q / e_q² − 1 ∈ 2R`. PROVED. -/
theorem quotientFactor_mul_inv_sq {F : Matrix (Fin 2) (Fin 2) R} {q qi a z zi ei m : R}
    (hq : q * qi = 1) (hz : z * zi = 1) (ha : F.trace = a) (hd : F.det = q)
    (hodd : q = 1 + 2 * m) (he : pointFactor a z zi * ei = 1) :
    quotientFactor F qi z zi * ei ^ 2 =
      1 + 2 * (m * (-(q + 1) * pointFactor a z zi ^ 2 + (q - 1) - (z + zi) * pointFactor a z zi)
        * qi ^ 2 * ei ^ 2) := by
  have key := sq_mul_quotientFactor hq hz ha hd
  set e := pointFactor a z zi
  set l := quotientFactor F qi z zi
  have hl : l = qi ^ 2 * (e ^ 2 + (q - 1) * (q - 1 - (z + zi) * e)) := by
    linear_combination (-(l * (q * qi + 1))) * hq + qi ^ 2 * key
  rw [hl]
  linear_combination (q * qi + 1) * (e * ei) ^ 2 * hq + (e * ei + 1) * he
    + ((-(q + 1) * e ^ 2 + (q - 1) - (z + zi) * e) * qi ^ 2 * ei ^ 2) * hodd

/-- **Conjugation fixes the point factor** (tex 4170–4171): `z ↦ z⁻¹` gives `e_q^c = e_q`;
the same swap is the orientation reversal of tex 4271–4272. PROVED. -/
theorem pointFactor_swap (a z zi : R) : pointFactor a zi z = pointFactor a z zi := by
  unfold pointFactor; ring

/-- **Orientation reversal fixes the quotient factor** (tex 4271–4272): replacing `z` by `z⁻¹`
leaves `l_q` unchanged. PROVED. -/
theorem quotientFactor_swap (F : Matrix (Fin 2) (Fin 2) R) (qi z zi : R) :
    quotientFactor F qi zi z = quotientFactor F qi z zi := by
  unfold quotientFactor; ring

/-- An element whose image in a field under a reduction killing the maximal ideal is nonzero
is a unit of the local ring. PROVED. -/
theorem isUnit_of_residue_ne_zero [IsLocalRing R] {k : Type*} [Field k] (ρ : R →+* k)
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal R, ρ x = 0) {x : R} (hx : ρ x ≠ 0) : IsUnit x :=
  IsLocalRing.notMem_maximalIdeal.mp fun hm => hx (hρ x hm)

variable {k : Type*} [Field k] [CharP k 2]

/-- **`ē_q = (1 + t) + (1 + t)⁻¹ = t²/(1 + t)`** (tex 4197–4204): under a reduction `ρ` to a field
of characteristic two with `ρ(a_q) = 0` (`a_q` is even, since `E[2]` is rational, tex 4200–4201)
and `ρ(z) = 1 + t`, the point factor satisfies `ρ(e_q) (1 + t) = t²`. PROVED. -/
theorem residue_pointFactor (ρ : R →+* k) {a z zi : R} (t : k) (hz : z * zi = 1)
    (ha : ρ a = 0) (hzt : ρ z = 1 + t) (ht : 1 + t ≠ 0) :
    ρ (pointFactor a z zi) * (1 + t) = t ^ 2 := by
  have hzi : ρ zi = (1 + t)⁻¹ := by
    have h := congrArg ρ hz
    rw [map_mul, map_one, hzt] at h
    exact eq_inv_of_mul_eq_one_right h
  have he : ρ (pointFactor a z zi) = 0 - (1 + t) - (1 + t)⁻¹ := by
    simp only [pointFactor, map_sub, ha, hzt, hzi]
  rw [he]
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hinv : (1 + t)⁻¹ * (1 + t) = 1 := inv_mul_cancel₀ ht
  linear_combination (-1 : k) * hinv + (-(1 + t + t ^ 2)) * h2

/-- **`ē_q ≠ 0`** in characteristic two when `t ≠ 0` (tex 4203–4204). PROVED. -/
theorem residue_pointFactor_ne_zero (ρ : R →+* k) {a z zi : R} {t : k} (hz : z * zi = 1)
    (ha : ρ a = 0) (hzt : ρ z = 1 + t) (ht : 1 + t ≠ 0) (ht0 : t ≠ 0) :
    ρ (pointFactor a z zi) ≠ 0 := by
  intro h0
  have := residue_pointFactor ρ t hz ha hzt ht
  rw [h0, zero_mul] at this
  exact ht0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this.symm)

/-- **`l̄_q = t⁴/(1 + t)²`** (tex 4284–4288): under the same reduction, with `ρ(q) = 1`,
`ρ(l_q) (1 + t)² = t⁴`; in particular the residual `t`-order of the two-place determinant
`q⁴ l_q` is four. PROVED. -/
theorem residue_quotientFactor (ρ : R →+* k) {F : Matrix (Fin 2) (Fin 2) R} {q qi a z zi : R}
    (t : k) (hq : q * qi = 1) (hz : z * zi = 1) (htr : F.trace = a) (hd : F.det = q)
    (ha : ρ a = 0) (hq1 : ρ q = 1) (hzt : ρ z = 1 + t) (ht : 1 + t ≠ 0) :
    ρ (quotientFactor F qi z zi) * (1 + t) ^ 2 = t ^ 4 := by
  have hzi : ρ zi = (1 + t)⁻¹ := by
    have h := congrArg ρ hz
    rw [map_mul, map_one, hzt] at h
    exact eq_inv_of_mul_eq_one_right h
  have hqi : ρ qi = 1 := by
    have h := congrArg ρ hq
    rw [map_mul, map_one, hq1, one_mul] at h
    exact h
  have hl : ρ (quotientFactor F qi z zi) = (1 + (1 + t) ^ 2) * (1 + ((1 + t)⁻¹) ^ 2) := by
    unfold quotientFactor
    rw [det_one_sub_smul, det_one_sub_smul, htr, hd]
    simp only [map_mul, map_sub, map_add, map_one, map_pow, ha, hq1, hqi, hzt, hzi]
    ring
  rw [hl]
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hinv : (1 + t)⁻¹ * (1 + t) = 1 := inv_mul_cancel₀ ht
  linear_combination (1 + (1 + t) ^ 2) * ((1 + t)⁻¹ * (1 + t) + 1) * hinv
    + ((2 + 2 * t) * t ^ 2 + 2 * (1 + t) ^ 2) * h2

/-- **`e_q` is a unit of `𝒪[G]`** (tex 4205): if `R` is local and the reduction `ρ` modulo the
maximal ideal `(2, I_G)` sends `a_q ↦ 0` and `z ↦ 1 + t` with `t ≠ 0`, `1 + t ≠ 0`, then
`e_q ∈ R^×`. That `𝒪[G]` is local with maximal ideal `(2, I_G)` and residue field `𝔽₂((t))` is the
setting of tex 4194–4197, carried here as the hypotheses on `R` and `ρ`. PROVED. -/
theorem isUnit_pointFactor [IsLocalRing R] (ρ : R →+* k)
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal R, ρ x = 0) {a z zi : R} {t : k} (hz : z * zi = 1)
    (ha : ρ a = 0) (hzt : ρ z = 1 + t) (ht : 1 + t ≠ 0) (ht0 : t ≠ 0) :
    IsUnit (pointFactor a z zi) :=
  isUnit_of_residue_ne_zero ρ hρ (residue_pointFactor_ne_zero ρ hz ha hzt ht ht0)

end EulerFactors

/-! ### The moving prime (tex 4066–4074) -/

section MovingPrime

/-- **`N_i = r_i + 1 − χ_h(r_i) a_{r_i} = (r_i − 1) − χ_h(r_i) m_i`** with
`m_i = a_{r_i} − 2χ_h(r_i)` (tex 4069–4071; `m_i` as in (4.5), tex 3912). PROVED. -/
theorem movingNorm_eq (r a χ : ℤ) (hχ : χ ^ 2 = 1) :
    r + 1 - χ * a = (r - 1) - χ * (a - 2 * χ) := by
  linear_combination (-2 : ℤ) * hχ

/-- The ultrametric equality for `v₂` on `ℤ`: if `2^{v₂ y + 1} ∣ x` and `y ≠ 0` then
`v₂(x + y) = v₂ y`. PROVED. -/
theorem padicValInt_add_of_dvd {x y : ℤ} (hy : y ≠ 0)
    (hx : (2 : ℤ) ^ (padicValInt 2 y + 1) ∣ x) : padicValInt 2 (x + y) = padicValInt 2 y := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hle : padicValInt 2 y + 1 ≤ padicValInt 2 x := by
    rcases (padicValInt_dvd_iff (p := 2) _ x).mp (by exact_mod_cast hx) with h | h
    · exact absurd h hx0
    · exact h
  have hY : (y : ℚ) ≠ 0 := by exact_mod_cast hy
  have hX : (x : ℚ) ≠ 0 := by exact_mod_cast hx0
  have hlt : padicValRat 2 (y : ℚ) < padicValRat 2 (x : ℚ) := by
    rw [padicValRat.of_int, padicValRat.of_int]; exact_mod_cast Nat.lt_of_succ_le hle
  have hsum : (y : ℚ) + x ≠ 0 := by
    intro h0
    have hxy : (x : ℚ) = -(y : ℚ) := by linarith
    rw [hxy, padicValRat.neg] at hlt
    exact lt_irrefl _ hlt
  have := padicValRat.add_eq_of_lt hsum hY hX hlt
  rw [show ((y : ℚ) + x) = ((x + y : ℤ) : ℚ) by push_cast; ring, padicValRat.of_int,
    padicValRat.of_int] at this
  exact_mod_cast this

/-- `v₂(χ m) = v₂ m` for `χ = ±1`. PROVED. -/
theorem padicValInt_sign_mul {χ m : ℤ} (hχ : χ = 1 ∨ χ = -1) :
    padicValInt 2 (χ * m) = padicValInt 2 m := by
  rcases hχ with rfl | rfl
  · simp
  · have h : padicValRat 2 ((-m : ℤ) : ℚ) = padicValRat 2 (m : ℚ) := by
      push_cast; exact padicValRat.neg _
    rw [padicValRat.of_int, padicValRat.of_int] at h
    simpa using (by exact_mod_cast h : padicValInt 2 (-m) = padicValInt 2 m)

/-- **Both local lengths at the moving prime equal `v₂ m_i`** (tex 4066–4074): with
`r_i ≡ 1 (mod 2^{B_i})`, `χ = χ_h(r_i) = ±1`, `m_i = a_{r_i} − 2χ ≠ 0` and `v₂ m_i < B_i` (the
manuscript has `v₂ m_i ≤ c_E < B_i`), `v₂ N_i = v₂ m_i`. PROVED. -/
theorem padicValInt_movingNorm {r a χ : ℤ} {B : ℕ} (hχ : χ = 1 ∨ χ = -1)
    (hm : a - 2 * χ ≠ 0) (hr : (2 : ℤ) ^ B ∣ r - 1) (hB : padicValInt 2 (a - 2 * χ) < B) :
    padicValInt 2 (r + 1 - χ * a) = padicValInt 2 (a - 2 * χ) := by
  have hχ2 : χ ^ 2 = 1 := by rcases hχ with rfl | rfl <;> norm_num
  rw [movingNorm_eq r a χ hχ2, sub_eq_add_neg, ← neg_mul]
  have hneg : (-χ = 1 ∨ -χ = -1) := by rcases hχ with rfl | rfl <;> simp
  have hy : -χ * (a - 2 * χ) ≠ 0 := mul_ne_zero (by rcases hχ with rfl | rfl <;> norm_num) hm
  rw [padicValInt_add_of_dvd hy, padicValInt_sign_mul hneg]
  rw [padicValInt_sign_mul hneg]
  exact (pow_dvd_pow 2 (Nat.succ_le_of_lt hB)).trans hr

end MovingPrime

end ZInQ.Manuscript.RC.Central
