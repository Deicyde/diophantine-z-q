import ZInQKernel.Model.Field.Valuation
import ZInQKernel.Model.Field.Units
import ZInQKernel.Model.Field.Residues

/-!
# The primes `(s)` and `(d)` of `ℤ[√2]`

Blueprint: `model/field/special-primes.md`.

1. `s` is prime, `2 = s²`, `ℤ[s]/(s) ≅ 𝔽₂` via `a₀ + a₁ s ↦ a₀ mod 2`, and
   `v_s(c₀ + c₁ s) = min (2 v₂(c₀), 2 v₂(c₁) + 1)` (with `v₂(0) = ∞`).
2. `d = 75 - 53 s` is prime, `N(d) = 7`, `ℤ[s]/(d) ≅ 𝔽₇` via `a₀ + a₁ s ↦ a₀ + 3 a₁ mod 7`, and
   `-1` is not a square in `𝔽₇`.
3. `δ = 3 - s = ε⁴ d` with `ε⁴ = 17 + 12 s`, so `v_d = v_δ`; `v_s(d) = v_s(δ) = v_s(ε) = 0`,
   `v_d(s) = v_d(2) = 0`, and `d`, `δ` are totally positive.
-/

namespace ZInQ

open QuadraticAlgebra K0

/-! ### Primes from prime norms -/

theorem Zs.isUnit_iff_natAbs_norm {z : Zs} : IsUnit z ↔ (QuadraticAlgebra.norm z).natAbs = 1 := by
  rw [Zs.isUnit_iff_norm, Int.natAbs_eq_iff]; simp

/-- An element of `ℤ[s]` whose norm is `±` a rational prime is prime. -/
theorem Zs.prime_of_natAbs_norm_prime {z : Zs} (h : (QuadraticAlgebra.norm z).natAbs.Prime) :
    Prime z := by
  apply irreducible_iff_prime.mp
  refine ⟨fun hu => h.ne_one (Zs.isUnit_iff_natAbs_norm.mp hu), fun a b hab => ?_⟩
  rw [hab, map_mul, Int.natAbs_mul, Nat.prime_mul_iff] at h
  rcases h with ⟨_, hb⟩ | ⟨_, ha⟩
  · exact Or.inr (Zs.isUnit_iff_natAbs_norm.mpr hb)
  · exact Or.inl (Zs.isUnit_iff_natAbs_norm.mpr ha)

/-! ### The prime `s` -/

theorem norm_sqrt2Z : QuadraticAlgebra.norm sqrt2Z = -2 := by
  rw [Zs.norm_eq]; simp [sqrt2Z]

theorem prime_sqrt2Z : Prime sqrt2Z :=
  Zs.prime_of_natAbs_norm_prime (by rw [norm_sqrt2Z]; norm_num)

/-- `2 = s²` in `ℤ[s]`. -/
theorem two_eq_sqrt2Z_sq : (2 : Zs) = sqrt2Z ^ 2 := by
  ext <;> simp [sqrt2Z, pow_two]

theorem zero_mul_zero_ZMod2 : (0 : ZMod 2) * 0 = (2 : ℤ) • 1 + (0 : ℤ) • 0 := by decide

/-- The residue map `ℤ[s] → 𝔽₂`, `a₀ + a₁ s ↦ a₀ mod 2`. -/
def residueTwo : Zs →+* ZMod 2 :=
  (QuadraticAlgebra.lift ⟨0, zero_mul_zero_ZMod2⟩).toRingHom

@[simp] theorem residueTwo_apply (z : Zs) : residueTwo z = (z.re : ZMod 2) := by
  simp [residueTwo]

theorem residueTwo_surjective : Function.Surjective residueTwo := by
  intro x; refine ⟨⟨x.val, 0⟩, ?_⟩; simp

theorem ker_residueTwo : RingHom.ker residueTwo = Ideal.span {sqrt2Z} := by
  ext z
  rw [RingHom.mem_ker, residueTwo_apply, Ideal.mem_span_singleton, ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨⟨z.im, k⟩, by ext <;> simp [sqrt2Z, hk]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c.im, by simp [sqrt2Z]⟩

/-- `ℤ[s]/(s) ≅ 𝔽₂`. -/
noncomputable def quotSqrt2Equiv : Zs ⧸ Ideal.span {sqrt2Z} ≃+* ZMod 2 :=
  (Ideal.quotEquivOfEq ker_residueTwo.symm).trans
    (RingHom.quotientKerEquivOfSurjective residueTwo_surjective)

theorem sqrt2Z_dvd_iff (z : Zs) : sqrt2Z ∣ z ↔ (2 : ℤ) ∣ z.re := by
  rw [← Ideal.mem_span_singleton, ← ker_residueTwo, RingHom.mem_ker, residueTwo_apply,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  rfl

/-! ### The valuation `v_s` -/

theorem toK0_natCast (n : ℕ) : Zs.toK0 (n : Zs) = (n : K0) := map_natCast _ n
theorem toK0_intCast (n : ℤ) : Zs.toK0 (n : Zs) = (n : K0) := map_intCast _ n

theorem vS_two : vp sqrt2Z 2 = 2 := by
  have : (2 : K0) = Zs.toK0 sqrt2Z ^ 2 := by rw [← map_pow, ← two_eq_sqrt2Z_sq, map_ofNat]
  rw [this, vp_pow prime_sqrt2Z, vp_self prime_sqrt2Z]; rfl

theorem vS_sqrt2 : vp sqrt2Z sqrt2 = 1 := by
  rw [← toK0_sqrt2Z]; exact vp_self prime_sqrt2Z

theorem vS_odd_nat {m : ℕ} (hm : Odd m) : vp sqrt2Z (m : K0) = 0 := by
  have hm0 : (m : Zs) ≠ 0 := by
    intro h; have := congrArg QuadraticAlgebra.re h; simp at this; subst this; simp at hm
  rw [← toK0_natCast, vp_eq_zero_iff prime_sqrt2Z hm0, sqrt2Z_dvd_iff]
  simp only [QuadraticAlgebra.re_natCast]
  exact_mod_cast hm.not_two_dvd_nat

theorem vS_nat {n : ℕ} (hn : n ≠ 0) : vp sqrt2Z (n : K0) = 2 * padicValNat 2 n := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have h2 : (2 : K0) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  have hmK : (m : K0) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, vp_mul prime_sqrt2Z h2 hmK,
    vp_pow prime_sqrt2Z, vS_two, vS_odd_nat hm, padicValNat.mul (pow_ne_zero _ two_ne_zero) hm0,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm.not_two_dvd_nat]
  push_cast; ring

theorem vS_int {n : ℤ} (hn : n ≠ 0) : vp sqrt2Z (n : K0) = 2 * padicValInt 2 n := by
  rcases Int.natAbs_eq n with h | h
  · rw [h, Int.cast_natCast, vS_nat (Int.natAbs_ne_zero.mpr hn), padicValInt.of_nat]
  · rw [h, Int.cast_neg, Int.cast_natCast, vp_neg prime_sqrt2Z,
      vS_nat (Int.natAbs_ne_zero.mpr hn), padicValInt, Int.natAbs_neg, Int.natAbs_natCast]

/-- `v_s(c) = 2 v₂(c)` for `c ∈ ℚ`, `c ≠ 0`. -/
theorem vS_rat {c : ℚ} (hc : c ≠ 0) : vp sqrt2Z (c : K0) = 2 * padicValRat 2 c := by
  have hnum : c.num ≠ 0 := Rat.num_ne_zero.mpr hc
  have hden : c.den ≠ 0 := c.den_nz
  have hc' : (c : K0) = (c.num : K0) / (c.den : K0) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  rw [hc', vp_div prime_sqrt2Z (Int.cast_ne_zero.mpr hnum) (Nat.cast_ne_zero.mpr hden),
    vS_int hnum, vS_nat hden, padicValRat_def]
  ring

/-- `v_s(c s) = 2 v₂(c) + 1` for `c ∈ ℚ`, `c ≠ 0`. -/
theorem vS_rat_mul_sqrt2 {c : ℚ} (hc : c ≠ 0) : vp sqrt2Z ((c : K0) * sqrt2) = 2 * padicValRat 2 c + 1 := by
  rw [vp_mul prime_sqrt2Z (Rat.cast_ne_zero.mpr hc) sqrt2_ne_zero, vS_rat hc, vS_sqrt2]

theorem K0.mk_eq (c₀ c₁ : ℚ) : (⟨c₀, c₁⟩ : K0) = (c₀ : K0) + (c₁ : K0) * sqrt2 := by
  ext <;> simp [sqrt2]

/-- `v_s(c₀ + c₁ s) = min (2 v₂(c₀)) (2 v₂(c₁) + 1)` for `c₀, c₁ ≠ 0`. -/
theorem vS_formula {c₀ c₁ : ℚ} (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) :
    vp sqrt2Z ⟨c₀, c₁⟩ = min (2 * padicValRat 2 c₀) (2 * padicValRat 2 c₁ + 1) := by
  rw [K0.mk_eq, vp_add_eq_min_of_ne prime_sqrt2Z (Rat.cast_ne_zero.mpr h₀)
    (mul_ne_zero (Rat.cast_ne_zero.mpr h₁) sqrt2_ne_zero), vS_rat h₀, vS_rat_mul_sqrt2 h₁]
  rw [vS_rat h₀, vS_rat_mul_sqrt2 h₁]; omega

/-- The `2`-adic valuation on `ℚ` with `v₂(0) = ∞`. -/
noncomputable def v2Top (c : ℚ) : WithTop ℤ := if c = 0 then ⊤ else ((padicValRat 2 c : ℤ) : WithTop ℤ)

/-- The formula for `v_s` in all cases: for `c₀, c₁ ∈ ℚ` not both zero,
`v_s(c₀ + c₁ s) = min (2 v₂(c₀)) (2 v₂(c₁) + 1)` with `v₂(0) = ∞`. -/
theorem vS_formula_withTop {c₀ c₁ : ℚ} (h : c₀ ≠ 0 ∨ c₁ ≠ 0) :
    ((vp sqrt2Z ⟨c₀, c₁⟩ : ℤ) : WithTop ℤ) = min (2 * v2Top c₀) (2 * v2Top c₁ + 1) := by
  by_cases h₀ : c₀ = 0
  · have h₁ : c₁ ≠ 0 := h.resolve_left (not_not.mpr h₀)
    subst h₀
    have : (⟨0, c₁⟩ : K0) = (c₁ : K0) * sqrt2 := by ext <;> simp [sqrt2]
    rw [this, vS_rat_mul_sqrt2 h₁]
    simp only [v2Top, ↓reduceIte, h₁]
    rw [WithTop.mul_top (by norm_num), min_eq_right le_top]
    norm_cast
  · by_cases h₁ : c₁ = 0
    · subst h₁
      have : (⟨c₀, 0⟩ : K0) = (c₀ : K0) := by ext <;> simp
      rw [this, vS_rat h₀]
      simp only [v2Top, ↓reduceIte, h₀]
      rw [WithTop.mul_top (by norm_num), WithTop.top_add, min_eq_left le_top]
      norm_cast
    · rw [vS_formula h₀ h₁]
      simp only [v2Top, h₀, h₁, ↓reduceIte]
      norm_cast

/-! ### The prime `d` -/

/-- `N(d) = 7`. -/
theorem norm_genDZ : QuadraticAlgebra.norm genDZ = 7 := by
  rw [Zs.norm_eq]; simp [genDZ]

theorem prime_genDZ : Prime genDZ :=
  Zs.prime_of_natAbs_norm_prime (by rw [norm_genDZ]; norm_num)

theorem three_mul_three_ZMod7 : (3 : ZMod 7) * 3 = (2 : ℤ) • 1 + (0 : ℤ) • 3 := by decide

/-- The residue map `ℤ[s] → 𝔽₇`, `a₀ + a₁ s ↦ a₀ + 3 a₁ mod 7`. -/
def residueSeven : Zs →+* ZMod 7 :=
  (QuadraticAlgebra.lift ⟨3, three_mul_three_ZMod7⟩).toRingHom

@[simp] theorem residueSeven_apply (z : Zs) :
    residueSeven z = (z.re : ZMod 7) + (z.im : ZMod 7) * 3 := by
  simp [residueSeven, zsmul_eq_mul]

theorem residueSeven_surjective : Function.Surjective residueSeven := by
  intro x; refine ⟨⟨x.val, 0⟩, ?_⟩; simp

/-- `δ = ε⁴ d` in `ℤ[s]`, with `ε⁴ = 17 + 12 s`. -/
theorem epsilonZ_pow_four : epsilonZ ^ 4 = ⟨17, 12⟩ := by decide

theorem deltaZ_eq : deltaZ = epsilonZ ^ 4 * genDZ := by decide

theorem genDZ_dvd_deltaZ : genDZ ∣ deltaZ := ⟨epsilonZ ^ 4, by rw [deltaZ_eq, mul_comm]⟩

theorem genDZ_dvd_seven : genDZ ∣ (7 : Zs) := ⟨⟨75, 53⟩, by decide⟩

theorem ker_residueSeven : RingHom.ker residueSeven = Ideal.span {genDZ} := by
  ext z
  rw [RingHom.mem_ker, residueSeven_apply, Ideal.mem_span_singleton]
  constructor
  · intro h
    have h7 : ((7 : ℕ) : ℤ) ∣ z.re + z.im * 3 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp (by push_cast; exact h)
    obtain ⟨k, hk⟩ := h7
    push_cast at hk
    -- `z = 7 k - a₁ δ`
    have hz : z = (7 : Zs) * k - (z.im : Zs) * deltaZ := by
      ext <;> simp [deltaZ]; linarith
    rw [hz]
    exact dvd_sub (dvd_mul_of_dvd_left genDZ_dvd_seven _) (dvd_mul_of_dvd_right genDZ_dvd_deltaZ _)
  · rintro ⟨c, rfl⟩
    rw [← residueSeven_apply, map_mul]
    have : residueSeven genDZ = 0 := by rw [residueSeven_apply]; decide
    rw [this, zero_mul]

/-- `ℤ[s]/(d) ≅ 𝔽₇`. -/
noncomputable def quotGenDEquiv : Zs ⧸ Ideal.span {genDZ} ≃+* ZMod 7 :=
  (Ideal.quotEquivOfEq ker_residueSeven.symm).trans
    (RingHom.quotientKerEquivOfSurjective residueSeven_surjective)

theorem genDZ_dvd_iff (z : Zs) : genDZ ∣ z ↔ residueSeven z = 0 := by
  rw [← Ideal.mem_span_singleton, ← ker_residueSeven, RingHom.mem_ker]

/-- `-1` is not a square in the residue field `ℤ[s]/(d) ≅ 𝔽₇`. -/
theorem not_isSquare_neg_one_mod_genD : ¬ IsSquare (-1 : Zs ⧸ Ideal.span {genDZ}) := by
  intro h
  apply not_isSquare_neg_one_zmod_seven
  have := h.map quotGenDEquiv
  simpa using this

/-! ### `δ`, `ε` and the valuations -/

theorem associated_genDZ_deltaZ : Associated genDZ deltaZ :=
  ⟨epsUnit ^ 4, by rw [Units.val_pow_eq_pow_val, epsUnit_val, deltaZ_eq, mul_comm]⟩

theorem prime_deltaZ : Prime deltaZ := associated_genDZ_deltaZ.prime prime_genDZ

/-- `v_d = v_δ`. -/
theorem vp_genDZ_eq_vp_deltaZ : vp genDZ = vp deltaZ := vp_eq_of_associated associated_genDZ_deltaZ

theorem vS_genD : vp sqrt2Z genD = 0 := by
  rw [← toK0_genDZ, vp_eq_zero_iff prime_sqrt2Z prime_genDZ.ne_zero, sqrt2Z_dvd_iff]
  simp [genDZ]

theorem vS_delta : vp sqrt2Z delta = 0 := by
  rw [← toK0_deltaZ, vp_eq_zero_iff prime_sqrt2Z prime_deltaZ.ne_zero, sqrt2Z_dvd_iff]
  simp [deltaZ]

theorem vS_epsilon : vp sqrt2Z epsilon = 0 := by
  rw [← toK0_epsilonZ, ← epsUnit_val]; exact vp_unit prime_sqrt2Z _

theorem vp_genDZ_sqrt2 : vp genDZ sqrt2 = 0 := by
  rw [← toK0_sqrt2Z, vp_eq_zero_iff prime_genDZ prime_sqrt2Z.ne_zero, genDZ_dvd_iff,
    residueSeven_apply]
  simp [sqrt2Z]; decide

theorem vp_genDZ_two : vp genDZ 2 = 0 := by
  have : (2 : K0) = Zs.toK0 2 := (map_ofNat _ 2).symm
  rw [this, vp_eq_zero_iff prime_genDZ two_ne_zero, genDZ_dvd_iff, residueSeven_apply]
  simp; decide

theorem fiftythree_mul_sqrt_two_lt : 53 * Real.sqrt 2 < 75 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith [Real.sqrt_nonneg 2]

/-- `d` is totally positive: `σ±(d) = 75 ∓ 53 √2 > 0`. -/
theorem totallyPositive_genD : TotallyPositive genD := by
  have := fiftythree_mul_sqrt_two_lt
  have h0 := Real.sqrt_nonneg 2
  constructor
  · rw [embPlus_apply]; simp [genD]; linarith
  · rw [embMinus_apply]; simp [genD]; linarith

/-- `δ` is totally positive: `σ±(δ) = 3 ∓ √2 > 0`. -/
theorem totallyPositive_delta : TotallyPositive delta := by
  obtain ⟨h1, h2⟩ := sqrt_two_bounds
  constructor
  · rw [embPlus_apply]; simp [delta]; linarith
  · rw [embMinus_apply]; simp [delta]; linarith

end ZInQ
