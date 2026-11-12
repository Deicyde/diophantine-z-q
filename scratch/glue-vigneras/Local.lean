import Mathlib

/-!
# glue-vigneras: local normalizers of the maximal order of `B = (2,-3)` at `p = 2, 3`

`B_p = ℍ[ℚ_[p], 2, 0, -3]`, `𝒪_p` = the `ℤ_p`-span of N5's basis `(1, i, (1+j)/2, (i+ij)/2)`.
-/

open Quaternion

attribute [local simp] QuaternionAlgebra.re_ofNat QuaternionAlgebra.imI_ofNat QuaternionAlgebra.imJ_ofNat QuaternionAlgebra.imK_ofNat

namespace GlueVigneras

section Unit
variable {p : ℕ} [hp : Fact p.Prime]

theorem norm_eq_one_of_toZMod_ne {z : ℤ_[p]} (h : PadicInt.toZMod z ≠ 0) : ‖z‖ = 1 := by
  by_contra hne
  have hlt : ‖z‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one z) hne
  have hm : z ∈ IsLocalRing.maximalIdeal ℤ_[p] := PadicInt.mem_nonunits.mpr hlt
  rw [← PadicInt.ker_toZMod] at hm
  exact h (RingHom.mem_ker.mp hm)

/-- A nonzero `p`-adic number has norm an integer power of `p`. -/
theorem norm_zpow {x : ℚ_[p]} (hx : x ≠ 0) : ∃ m : ℤ, ‖x‖ = (p : ℝ) ^ m :=
  ⟨_, Padic.norm_eq_zpow_neg_valuation hx⟩

theorem norm_zero_or_zpow (x : ℚ_[p]) : ‖x‖ = 0 ∨ ∃ m : ℤ, ‖x‖ = (p : ℝ) ^ m := by
  by_cases hx : x = 0
  · left; simp [hx]
  · right; exact norm_zpow hx

theorem max_zero_or_zpow (x y : ℚ_[p]) :
    max ‖x‖ ‖y‖ = 0 ∨ ∃ m : ℤ, max ‖x‖ ‖y‖ = (p : ℝ) ^ m := by
  rcases le_total ‖x‖ ‖y‖ with h | h
  · rw [max_eq_right h]; exact norm_zero_or_zpow y
  · rw [max_eq_left h]; exact norm_zero_or_zpow x

/-- A homogeneous binary quadratic form whose dehomogenizations take unit values on `ℤ_p` has
`‖Q x y‖ = max(‖x‖, ‖y‖)²`. -/
theorem norm_binary (Q : ℚ_[p] → ℚ_[p] → ℚ_[p])
    (hom : ∀ s x y, Q (s * x) (s * y) = s ^ 2 * Q x y)
    (h1 : ∀ t : ℚ_[p], ‖t‖ ≤ 1 → ‖Q 1 t‖ = 1) (h2 : ∀ t : ℚ_[p], ‖t‖ ≤ 1 → ‖Q t 1‖ = 1)
    (x y : ℚ_[p]) : ‖Q x y‖ = (max ‖x‖ ‖y‖) ^ 2 := by
  rcases le_total ‖y‖ ‖x‖ with h | h
  · rw [max_eq_left h]
    by_cases hx : x = 0
    · have hy : y = 0 := by simpa [hx] using h
      have := hom 0 0 0
      simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
      simp [hx, hy, this]
    · have hxn : ‖x‖ ≠ 0 := by simpa using hx
      have e : Q x y = x ^ 2 * Q 1 (y / x) := by
        rw [← hom]; congr 1 <;> field_simp
      rw [e, norm_mul, norm_pow, h1 _ (by rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _))]
      ring
  · rw [max_eq_right h]
    by_cases hy : y = 0
    · have hx : x = 0 := by simpa [hy] using h
      have := hom 0 0 0
      simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
      simp [hx, hy, this]
    · have e : Q x y = y ^ 2 * Q (x / y) 1 := by
        rw [← hom]; congr 1 <;> field_simp
      rw [e, norm_mul, norm_pow, h2 _ (by rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _))]
      ring

/-- Lift a `p`-adic number of norm `≤ 1` to `ℤ_p`. -/
def lift (t : ℚ_[p]) (ht : ‖t‖ ≤ 1) : ℤ_[p] := ⟨t, ht⟩

theorem coe_lift (t : ℚ_[p]) (ht : ‖t‖ ≤ 1) : ((lift t ht : ℤ_[p]) : ℚ_[p]) = t := rfl

@[simp] theorem coe_two : ((2 : ℤ_[p]) : ℚ_[p]) = 2 := by
  have := PadicInt.coe_natCast (p := p) 2; simpa using this

end Unit

/-- At `p = 3`: `‖a² - 2b²‖ = max(‖a‖,‖b‖)²` (2 is not a square mod 3). -/
theorem norm_form3 (a b : ℚ_[3]) : ‖a ^ 2 - 2 * b ^ 2‖ = (max ‖a‖ ‖b‖) ^ 2 := by
  apply norm_binary (fun x y => x ^ 2 - 2 * y ^ 2) (fun s x y => by ring)
  · intro t ht
    have e : (1 : ℚ_[3]) ^ 2 - 2 * t ^ 2 = ((1 - 2 * (lift t ht) ^ 2 : ℤ_[3]) : ℚ_[3]) := by
      push_cast [coe_lift, coe_two]; ring
    rw [e, ← PadicInt.norm_def]
    apply norm_eq_one_of_toZMod_ne
    rw [map_sub, map_one, map_mul, map_pow, map_ofNat]
    generalize PadicInt.toZMod (lift t ht) = s
    revert s; decide
  · intro t ht
    have e : t ^ 2 - 2 * (1 : ℚ_[3]) ^ 2 = (((lift t ht) ^ 2 - 2 : ℤ_[3]) : ℚ_[3]) := by
      push_cast [coe_lift, coe_two]; ring
    rw [e, ← PadicInt.norm_def]
    apply norm_eq_one_of_toZMod_ne
    rw [map_sub, map_pow, map_ofNat]
    generalize PadicInt.toZMod (lift t ht) = s
    revert s; decide

/-- At `p = 2`: `‖x² + xy + y²‖ = max(‖x‖,‖y‖)²` (the norm form of `ℤ₂[ω]`). -/
theorem norm_form2 (a b : ℚ_[2]) : ‖a ^ 2 + a * b + b ^ 2‖ = (max ‖a‖ ‖b‖) ^ 2 := by
  apply norm_binary (fun x y => x ^ 2 + x * y + y ^ 2) (fun s x y => by ring)
  · intro t ht
    have e : (1 : ℚ_[2]) ^ 2 + 1 * t + t ^ 2 = ((1 + (lift t ht) + (lift t ht) ^ 2 : ℤ_[2]) : ℚ_[2]) := by
      push_cast [coe_lift, coe_two]; ring
    rw [e, ← PadicInt.norm_def]
    apply norm_eq_one_of_toZMod_ne
    rw [map_add, map_add, map_one, map_pow]
    generalize PadicInt.toZMod (lift t ht) = s
    revert s; decide
  · intro t ht
    have e : t ^ 2 + t * 1 + (1 : ℚ_[2]) ^ 2 = (((lift t ht) ^ 2 + (lift t ht) + 1 : ℤ_[2]) : ℚ_[2]) := by
      push_cast [coe_lift, coe_two]; ring
    rw [e, ← PadicInt.norm_def]
    apply norm_eq_one_of_toZMod_ne
    rw [map_add, map_add, map_one, map_pow]
    generalize PadicInt.toZMod (lift t ht) = s
    revert s; decide

section Key
variable {p : ℕ} [hp : Fact p.Prime]

theorem norm_le_one_of_eq_coe {x : ℚ_[p]} (z : ℤ_[p]) (h : x = z) : ‖x‖ ≤ 1 := by
  rw [h]; exact PadicInt.norm_le_one z

theorem one_lt_p : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt

/-- The valuation-parity step: if `‖u‖ = M₁²` (an even power of `p`, or `0`) and
`‖v‖ = M₂²/p` (an odd power, or `0`), then `‖u + v‖ ≤ 1` forces `M₁ ≤ 1` and `M₂ ≤ 1`. -/
theorem key (u v : ℚ_[p]) (M1 M2 : ℝ) (h1 : ‖u‖ = M1 ^ 2) (h2 : ‖v‖ = M2 ^ 2 / p)
    (hM1 : M1 = 0 ∨ ∃ m : ℤ, M1 = (p : ℝ) ^ m) (hM2 : M2 = 0 ∨ ∃ m : ℤ, M2 = (p : ℝ) ^ m)
    (h : ‖u + v‖ ≤ 1) : M1 ≤ 1 ∧ M2 ≤ 1 := by
  have p1 := one_lt_p (p := p)
  have p0 : (0 : ℝ) < p := by linarith
  have sq : ∀ m : ℤ, ((p : ℝ) ^ m) ^ 2 = (p : ℝ) ^ (2 * m) := by
    intro m; rw [← zpow_natCast, ← zpow_mul]; ring_nf
  have hdiv : ∀ m : ℤ, ((p : ℝ) ^ m) ^ 2 / p = (p : ℝ) ^ (2 * m - 1) := by
    intro m; rw [sq, zpow_sub_one₀ p0.ne']; field_simp
  rcases hM1 with h0 | ⟨m, rfl⟩ <;> rcases hM2 with h0' | ⟨n, rfl⟩
  · simp [h0, h0']
  · -- `u = 0`
    have hu : u = 0 := by simpa [h0] using h1
    rw [hu, zero_add, h2, hdiv] at h
    refine ⟨by simp [h0], ?_⟩
    have : 2 * n - 1 ≤ 0 := by
      by_contra hc; push Not at hc
      have := one_lt_zpow₀ p1 hc; linarith
    exact zpow_le_one_of_nonpos₀ p1.le (by omega)
  · have hv : v = 0 := by simpa [h0'] using h2
    rw [hv, add_zero, h1, sq] at h
    refine ⟨?_, by simp [h0']⟩
    have : 2 * m ≤ 0 := by
      by_contra hc; push Not at hc
      have := one_lt_zpow₀ p1 hc; linarith
    exact zpow_le_one_of_nonpos₀ p1.le (by omega)
  · have hne : ‖u‖ ≠ ‖v‖ := by
      rw [h1, h2, sq, hdiv]; intro he
      have := zpow_right_injective₀ p0 p1.ne' he
      omega
    rw [Padic.add_eq_max_of_ne hne] at h
    have hu := (le_max_left _ _).trans h
    have hv := (le_max_right _ _).trans h
    rw [h1, sq] at hu; rw [h2, hdiv] at hv
    have a1 : 2 * m ≤ 0 := by
      by_contra hc; push Not at hc
      have := one_lt_zpow₀ p1 hc; linarith
    have a2 : 2 * n - 1 ≤ 0 := by
      by_contra hc; push Not at hc
      have := one_lt_zpow₀ p1 hc; linarith
    exact ⟨zpow_le_one_of_nonpos₀ p1.le (by omega), zpow_le_one_of_nonpos₀ p1.le (by omega)⟩

end Key

section Alg
variable (p : ℕ) [hp : Fact p.Prime]

/-- `B_p = B ⊗ ℚ_p = ℍ[ℚ_[p], 2, 0, -3]` (`i² = 2`, `j² = -3`, `k = ij`). -/
abbrev Bp := ℍ[ℚ_[p], 2, 0, -3]

/-- The `ℤ_p`-combination `n₀ + n₁ i + n₂ (1+j)/2 + n₃ (i+ij)/2` of N5's basis. -/
noncomputable def combp (n : Fin 4 → ℤ_[p]) : Bp p :=
  ⟨(n 0 : ℚ_[p]) + (n 2 : ℚ_[p]) / 2, (n 1 : ℚ_[p]) + (n 3 : ℚ_[p]) / 2,
    (n 2 : ℚ_[p]) / 2, (n 3 : ℚ_[p]) / 2⟩

/-- `𝒪_p = 𝒪 ⊗ ℤ_p`: the `ℤ_p`-span of N5's basis. -/
def Op : Set (Bp p) := Set.range (combp p)

/-- Coordinates in N5's basis. -/
noncomputable def coord (x : Bp p) : Fin 4 → ℚ_[p] := ![x.re - x.imJ, x.imI - x.imK, 2 * x.imJ, 2 * x.imK]

theorem mem_Op_iff_coord (x : Bp p) : x ∈ Op p ↔ ∀ k, ‖coord p x k‖ ≤ 1 := by
  constructor
  · rintro ⟨n, rfl⟩ k
    have e : coord p (combp p n) k = (n k : ℚ_[p]) := by
      fin_cases k <;> simp [coord, combp] <;> ring
    rw [e]; exact PadicInt.norm_le_one _
  · intro h
    refine ⟨fun k => lift (coord p x k) (h k), ?_⟩
    ext <;> simp [combp, coord, coe_lift] <;> ring

/-- Reduced norm `nrd x = x x̄`. -/
noncomputable def nrd (x : Bp p) : ℚ_[p] := (x * star x).re

theorem nrd_eq (x : Bp p) :
    nrd p x = x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 := by
  simp [nrd]; ring

theorem mul_star_eq (x : Bp p) : x * star x = algebraMap ℚ_[p] (Bp p) (nrd p x) := by
  ext <;> simp [nrd] <;> ring

theorem nrd_mul (x y : Bp p) : nrd p (x * y) = nrd p x * nrd p y := by
  simp only [nrd_eq]; simp; ring

theorem nrd_one : nrd p 1 = 1 := by simp [nrd_eq]

theorem nrd_smul (c : ℚ_[p]) (x : Bp p) : nrd p (c • x) = c ^ 2 * nrd p x := by
  simp only [nrd_eq]; simp; ring

theorem nrd_coord (x : Bp p) :
    nrd p x = (coord p x 0 ^ 2 + coord p x 0 * coord p x 2 + coord p x 2 ^ 2)
      + (-2) * (coord p x 1 ^ 2 + coord p x 1 * coord p x 3 + coord p x 3 ^ 2) := by
  simp [nrd_eq, coord]; ring

/-- Elements of `𝒪_p` have integral reduced norm (any `p`). -/
theorem norm_nrd_le_one_of_mem {x : Bp p} (hx : x ∈ Op p) : ‖nrd p x‖ ≤ 1 := by
  rw [mem_Op_iff_coord] at hx
  rw [nrd_coord]
  set n : Fin 4 → ℤ_[p] := fun k => lift (coord p x k) (hx k)
  have hn : ∀ k, coord p x k = n k := fun k => rfl
  apply norm_le_one_of_eq_coe ((n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2) + (-2) * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2))
  simp only [hn]; push_cast [coe_two]; ring

end Alg

theorem norm_two_two : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by simpa using Padic.norm_p (p := 2)
theorem norm_three_three : ‖(3 : ℚ_[3])‖ = 3⁻¹ := by simpa using Padic.norm_p (p := 3)

/-- **`p = 2`.** `𝒪₂ = {x ∈ B₂ : nrd x ∈ ℤ₂}`. -/
theorem mem_Op_iff_nrd_two (x : Bp 2) : x ∈ Op 2 ↔ ‖nrd 2 x‖ ≤ 1 := by
  refine ⟨norm_nrd_le_one_of_mem 2, fun h => ?_⟩
  rw [nrd_coord] at h
  have k := key (p := 2) _ _ (max ‖coord 2 x 0‖ ‖coord 2 x 2‖) (max ‖coord 2 x 1‖ ‖coord 2 x 3‖)
    (norm_form2 _ _) ?_ (max_zero_or_zpow _ _) (max_zero_or_zpow _ _) h
  · rw [mem_Op_iff_coord]; intro i
    fin_cases i
    · exact (le_max_left _ _).trans k.1
    · exact (le_max_left _ _).trans k.2
    · exact (le_max_right _ _).trans k.1
    · exact (le_max_right _ _).trans k.2
  · rw [norm_mul, norm_form2, norm_neg, norm_two_two]; push_cast; ring

/-- **`p = 3`.** `𝒪₃ = {x ∈ B₃ : nrd x ∈ ℤ₃}`. -/
theorem mem_Op_iff_nrd_three (x : Bp 3) : x ∈ Op 3 ↔ ‖nrd 3 x‖ ≤ 1 := by
  refine ⟨norm_nrd_le_one_of_mem 3, fun h => ?_⟩
  have e : nrd 3 x = (x.re ^ 2 - 2 * x.imI ^ 2) + 3 * (x.imJ ^ 2 - 2 * x.imK ^ 2) := by
    rw [nrd_eq]; ring
  rw [e] at h
  have k := key (p := 3) _ _ (max ‖x.re‖ ‖x.imI‖) (max ‖x.imJ‖ ‖x.imK‖)
    (norm_form3 _ _) ?_ (max_zero_or_zpow _ _) (max_zero_or_zpow _ _) h
  · have ha := (le_max_left _ _).trans k.1
    have hb := (le_max_right _ _).trans k.1
    have hc := (le_max_left _ _).trans k.2
    have hd := (le_max_right _ _).trans k.2
    rw [mem_Op_iff_coord]; intro i
    fin_cases i
    · exact norm_le_one_of_eq_coe (lift _ ha - lift _ hc) (by simp [coord, coe_lift])
    · exact norm_le_one_of_eq_coe (lift _ hb - lift _ hd) (by simp [coord, coe_lift])
    · exact norm_le_one_of_eq_coe (2 * lift _ hc) (by simp [coord, coe_lift, coe_two])
    · exact norm_le_one_of_eq_coe (2 * lift _ hd) (by simp [coord, coe_lift, coe_two])
  · rw [norm_mul, norm_form3, norm_three_three]; push_cast; ring

section Normalizer
variable (p : ℕ) [hp : Fact p.Prime]

theorem mem_Op_iff_nrd (hp2 : p = 2 ∨ p = 3) (x : Bp p) : x ∈ Op p ↔ ‖nrd p x‖ ≤ 1 := by
  rcases hp2 with rfl | rfl
  · exact mem_Op_iff_nrd_two x
  · exact mem_Op_iff_nrd_three x

theorem nrd_unit_mul_inv (u : (Bp p)ˣ) : nrd p u * nrd p ((u⁻¹ : (Bp p)ˣ) : Bp p) = 1 := by
  rw [← nrd_mul, Units.mul_inv, nrd_one]

theorem norm_nrd_unit_mul_inv (u : (Bp p)ˣ) :
    ‖nrd p u‖ * ‖nrd p ((u⁻¹ : (Bp p)ˣ) : Bp p)‖ = 1 := by
  rw [← norm_mul, nrd_unit_mul_inv, norm_one]

theorem nrd_unit_ne_zero (u : (Bp p)ˣ) : nrd p u ≠ 0 := by
  intro h; have := nrd_unit_mul_inv p u; rw [h, zero_mul] at this; exact zero_ne_one this

/-- `𝒪_p^×`: the units of `B_p` lying in `𝒪_p` together with their inverses. -/
def OpUnits : Set (Bp p)ˣ := {u | (u : Bp p) ∈ Op p ∧ ((u⁻¹ : (Bp p)ˣ) : Bp p) ∈ Op p}

/-- The normalizer of `𝒪_p` in `B_p^×`: `x 𝒪_p x⁻¹ = 𝒪_p`. -/
def normalizerOp : Set (Bp p)ˣ :=
  {x | ∀ y : Bp p, y ∈ Op p ↔ (x : Bp p) * y * ((x⁻¹ : (Bp p)ˣ) : Bp p) ∈ Op p}

/-- `ℚ_p^× 𝒪_p^×` (as a set). -/
def scalOpUnits : Set (Bp p)ˣ :=
  {x | ∃ c : ℚ_[p]ˣ, ∃ u ∈ OpUnits p, (x : Bp p) = (c : ℚ_[p]) • (u : Bp p)}

theorem mem_OpUnits_iff (hp2 : p = 2 ∨ p = 3) (u : (Bp p)ˣ) : u ∈ OpUnits p ↔ ‖nrd p u‖ = 1 := by
  have h := norm_nrd_unit_mul_inv p u
  have h0 := norm_nonneg (nrd p u)
  have h0' := norm_nonneg (nrd p ((u⁻¹ : (Bp p)ˣ) : Bp p))
  simp only [OpUnits, Set.mem_ofPred_eq, mem_Op_iff_nrd p hp2]
  constructor
  · rintro ⟨h1, h2⟩; nlinarith
  · intro h1; rw [h1, one_mul] at h; exact ⟨h1.le, h.le⟩

/-- **The normalizer of `𝒪_p` is all of `B_p^×`** (`p = 2, 3`). -/
theorem normalizerOp_eq_univ (hp2 : p = 2 ∨ p = 3) : normalizerOp p = Set.univ := by
  ext x
  simp only [normalizerOp, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  intro y
  rw [mem_Op_iff_nrd p hp2, mem_Op_iff_nrd p hp2, nrd_mul, nrd_mul]
  have := nrd_unit_mul_inv p x
  have e : nrd p x * nrd p y * nrd p ((x⁻¹ : (Bp p)ˣ) : Bp p) = nrd p y := by
    linear_combination (nrd p y) * this
  rw [e]

theorem norm_p_zpow' (m : ℤ) : ‖(p : ℚ_[p]) ^ (-m)‖ = (p : ℝ) ^ m := by
  rw [Padic.norm_p_zpow, neg_neg]

/-- `x ∈ ℚ_p^× 𝒪_p^×` iff `v_p(nrd x)` is even. -/
theorem mem_scalOpUnits_iff (hp2 : p = 2 ∨ p = 3) (x : (Bp p)ˣ) :
    x ∈ scalOpUnits p ↔ ∃ m : ℤ, ‖nrd p x‖ = (p : ℝ) ^ (2 * m) := by
  have p0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  constructor
  · rintro ⟨c, u, hu, hx⟩
    rw [mem_OpUnits_iff p hp2] at hu
    obtain ⟨m, hm⟩ := norm_zpow (Units.ne_zero c)
    refine ⟨m, ?_⟩
    rw [hx, nrd_smul, norm_mul, norm_pow, hu, hm, mul_one, ← zpow_natCast, ← zpow_mul]
    ring_nf
  · rintro ⟨m, hm⟩
    have hc : ((p : ℚ_[p]) ^ (-m)) ≠ 0 := by
      apply zpow_ne_zero; exact_mod_cast hp.out.ne_zero
    let c : ℚ_[p]ˣ := Units.mk0 _ hc
    let u : (Bp p)ˣ := Units.map (algebraMap ℚ_[p] (Bp p)).toMonoidHom c⁻¹ * x
    have hu : (u : Bp p) = ((c⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) • (x : Bp p) := by
      simp [u, Algebra.smul_def]
    refine ⟨c, u, ?_, ?_⟩
    · rw [mem_OpUnits_iff p hp2, hu, nrd_smul, norm_mul, norm_pow, hm, Units.val_inv_eq_inv_val,
        norm_inv]
      simp only [c, Units.val_mk0, norm_p_zpow']
      have sq : ((p : ℝ) ^ m) ^ 2 = (p : ℝ) ^ (2 * m) := by
        rw [← zpow_natCast, ← zpow_mul]; ring_nf
      rw [inv_pow, sq, inv_mul_cancel₀ (zpow_pos p0 _).ne']
    · rw [hu, smul_smul, Units.mul_inv, one_smul]

/-- `ℚ_p^× 𝒪_p^×` as a subgroup of `B_p^×`. -/
def scalOpUnitsSubgroup (hp2 : p = 2 ∨ p = 3) : Subgroup (Bp p)ˣ where
  carrier := scalOpUnits p
  one_mem' := by
    rw [mem_scalOpUnits_iff p hp2]; exact ⟨0, by simp [nrd_one]⟩
  mul_mem' := by
    intro a b ha hb
    rw [mem_scalOpUnits_iff p hp2] at ha hb ⊢
    obtain ⟨m, hm⟩ := ha; obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    have p0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    rw [Units.val_mul, nrd_mul, norm_mul, hm, hn, ← zpow_add₀ p0.ne']; ring_nf
  inv_mem' := by
    intro a ha
    rw [mem_scalOpUnits_iff p hp2] at ha ⊢
    obtain ⟨m, hm⟩ := ha
    refine ⟨-m, ?_⟩
    have p0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    have h := norm_nrd_unit_mul_inv p a
    rw [hm] at h
    rw [eq_comm, ← mul_left_cancel_iff_of_pos (zpow_pos p0 (2 * m)), h, ← zpow_add₀ p0.ne']
    ring_nf; simp

/-- A uniformizer of `B_p`: a unit with `v_p(nrd π) = 1` (`π = i` at `p = 2`, `π = j` at `p = 3`). -/
theorem exists_pi (hp2 : p = 2 ∨ p = 3) : ∃ π : (Bp p)ˣ, ‖nrd p π‖ = (p : ℝ)⁻¹ := by
  rcases hp2 with rfl | rfl
  · refine ⟨⟨⟨0, 1, 0, 0⟩, ⟨0, 1/2, 0, 0⟩, ?_, ?_⟩, ?_⟩
    · ext <;> simp <;> norm_num
    · ext <;> simp <;> norm_num
    · simp only [nrd_eq]; norm_num
      rw [norm_two_two]; norm_num
  · refine ⟨⟨⟨0, 0, 1, 0⟩, ⟨0, 0, -1/3, 0⟩, ?_, ?_⟩, ?_⟩
    · ext <;> simp <;> norm_num
    · ext <;> simp <;> norm_num
    · simp only [nrd_eq]; norm_num
      rw [norm_three_three]; norm_num

/-- **Index two.** `[B_p^× : ℚ_p^× 𝒪_p^×] = 2` for `p = 2, 3`. -/
theorem index_scalOpUnits (hp2 : p = 2 ∨ p = 3) : (scalOpUnitsSubgroup p hp2).index = 2 := by
  have p0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have p1 := one_lt_p (p := p)
  rw [Subgroup.index_eq_two_iff]
  obtain ⟨π, hπ⟩ := exists_pi p hp2
  refine ⟨π, fun b => ?_⟩
  obtain ⟨k, hk⟩ := norm_zpow (nrd_unit_ne_zero p b)
  have m1 : b * π ∈ scalOpUnitsSubgroup p hp2 ↔ ∃ m : ℤ, k - 1 = 2 * m := by
    show b * π ∈ scalOpUnits p ↔ _
    rw [mem_scalOpUnits_iff p hp2, Units.val_mul, nrd_mul, norm_mul, hk, hπ, ← zpow_neg_one,
      ← zpow_add₀ p0.ne']
    constructor
    · rintro ⟨m, hm⟩; exact ⟨m, by have := zpow_right_injective₀ p0 p1.ne' hm; omega⟩
    · rintro ⟨m, hm⟩; exact ⟨m, by rw [← hm]; ring_nf⟩
  have m2 : b ∈ scalOpUnitsSubgroup p hp2 ↔ ∃ m : ℤ, k = 2 * m := by
    show b ∈ scalOpUnits p ↔ _
    rw [mem_scalOpUnits_iff p hp2, hk]
    constructor
    · rintro ⟨m, hm⟩; exact ⟨m, zpow_right_injective₀ p0 p1.ne' hm⟩
    · rintro ⟨m, hm⟩; exact ⟨m, by rw [hm]⟩
  rw [m1, m2]
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · exact Or.inr ⟨⟨n, rfl⟩, fun ⟨m, hm⟩ => by omega⟩
  · exact Or.inl ⟨⟨n, by ring⟩, fun ⟨m, hm⟩ => by omega⟩

/-- **Vignéras' local normalizer facts at the ramified primes of `B = (2,-3)`, instance.**
For `p ∈ {2, 3}`: the normalizer of `𝒪_p = 𝒪 ⊗ ℤ_p` in `B_p^×` is all of `B_p^×`, and
`ℚ_p^× 𝒪_p^×` has index 2 in it. -/
theorem vigneras_local (hp2 : p = 2 ∨ p = 3) :
    normalizerOp p = Set.univ ∧ (scalOpUnitsSubgroup p hp2 : Set (Bp p)ˣ) = scalOpUnits p ∧
      (scalOpUnitsSubgroup p hp2).index = 2 :=
  ⟨normalizerOp_eq_univ p hp2, rfl, index_scalOpUnits p hp2⟩

end Normalizer

end GlueVigneras
