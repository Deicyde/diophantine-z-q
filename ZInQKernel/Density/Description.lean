import ZInQKernel.Density.CharSum

/-!
# The arithmetic description of the good slope primes

File 2 of `docs/research/pd-paper.md` §6 (Proposition 1.6 of §1.3). For a prime `p` with
`p ≡ 1 (mod 8)` and `p mod 7 ∈ {3, 5, 6}` (`InClass p`) put `c_p = φ_p(1)/2` (`cp p`). Then

* `cp_odd`, `exists_sq_add_sq`: `c_p` is odd and `p = c_p² + e_p²` with `e_p = φ_p(r₀)/2`;
* `pointCount_pair`: for every `r` with `r² = 2`, the two point counts of `GoodSlopePrime` are
  `p + 1 - 2c_p` and `p + 1 + 2c_p`, in some order;
* `gcd_pointCount_eq`: their gcd is `4 · gcd(c_p, p + 1)`;
* `goodSlopePrime_of_gcd`, `goodSlopePrime_iff`: `GoodSlopePrime p ↔ gcd(c_p, p + 1) = 1`;
* `mod_four_of_dvd_cp`: an odd prime dividing `c_p` and `p + 1` is `≡ 1 (mod 4)`;
* `goodSlopePrime_seventeen'`: the sanity check `GoodSlopePrime 17` from `c_17 = -1`.
-/

namespace ZInQ.Density

open Finset

/-- The residue classes of Proposition 1.6: `p ≡ 1 (mod 8)` and `(p/7) = -1`. -/
def InClass (p : ℕ) : Prop := p % 8 = 1 ∧ (p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6)

instance : DecidablePred InClass := fun p => by unfold InClass; infer_instance

/-- `c_p = φ_p(1)/2` for `p` prime (and `0` otherwise). -/
noncomputable def cp (p : ℕ) : ℤ :=
  if h : p.Prime then haveI : Fact p.Prime := ⟨h⟩; jac (1 : ZMod p) / 2 else 0

theorem InClass.mod_four {p : ℕ} (hC : InClass p) : p % 4 = 1 := by
  unfold InClass at hC; omega

theorem InClass.ne_two {p : ℕ} (hC : InClass p) : p ≠ 2 := by
  unfold InClass at hC; omega

theorem InClass.ne_seven {p : ℕ} (hC : InClass p) : p ≠ 7 := by
  unfold InClass at hC; omega

/-! ### The gcd of `n - 2c` and `n + 2c` -/

/-- For `c` odd and `n ≡ 2 (mod 4)`: `gcd(n - 2c, n + 2c) = 4 gcd(c, n)`. -/
theorem int_gcd_sub_add_two_mul (c n : ℤ) (hc : c % 2 = 1) (hn : n % 4 = 2) :
    Int.gcd (n - 2 * c) (n + 2 * c) = 4 * Int.gcd c n := by
  obtain ⟨k, hk⟩ : ∃ k, n - 2 * c = 4 * k := ⟨(n - 2 * c) / 4, by omega⟩
  have h1 : n + 2 * c = 4 * (k + c) := by omega
  have h2 : n = 4 * k + 2 * c := by omega
  rw [hk, h1, Int.gcd_mul_left, Int.gcd_self_add_right, h2, Int.gcd_add_mul_right_right,
    Int.gcd_comm k c]
  have hcop : Nat.Coprime (4 : ℤ).natAbs c.natAbs := by
    have h2c : ¬ 2 ∣ c.natAbs := by omega
    exact Nat.Coprime.pow_left 2 (Nat.prime_two.coprime_iff_not_dvd.mpr h2c)
  rw [Int.gcd_eq_natAbs_gcd_natAbs c (4 * k), Int.natAbs_mul,
    Nat.Coprime.gcd_mul_left_cancel_right _ hcop]
  rfl

/-- The same for natural numbers equal to `n ∓ 2c` in either order. -/
theorem nat_gcd_eq_of_sub_add (A B : ℕ) (c n : ℤ) (hc : c % 2 = 1) (hn : n % 4 = 2)
    (h : ((A : ℤ) = n - 2 * c ∧ (B : ℤ) = n + 2 * c) ∨
      ((A : ℤ) = n + 2 * c ∧ (B : ℤ) = n - 2 * c)) :
    Nat.gcd A B = 4 * Int.gcd c n := by
  rw [← Int.gcd_natCast_natCast]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, int_gcd_sub_add_two_mul c n hc hn]
  · rw [h1, h2, Int.gcd_comm, int_gcd_sub_add_two_mul c n hc hn]

theorem not_isSquare_three_zmod_seven : ¬ IsSquare ((3 : ℕ) : ZMod 7) := by decide
theorem not_isSquare_five_zmod_seven : ¬ IsSquare ((5 : ℕ) : ZMod 7) := by decide
theorem not_isSquare_six_zmod_seven : ¬ IsSquare ((6 : ℕ) : ZMod 7) := by decide

/-! ### Proposition 1.6 -/

section

variable {p : ℕ} [Fact p.Prime]

local notation "χ" => quadraticChar (ZMod p)

theorem cp_eq : cp p = jac (1 : ZMod p) / 2 := by
  simp [cp, (Fact.out : p.Prime)]

theorem jac_one_eq (hp2 : p ≠ 2) : jac (1 : ZMod p) = 2 * cp p := by
  rw [cp_eq]
  obtain ⟨k, hk⟩ := jac_even hp2 (1 : ZMod p)
  omega

/-- `χ(7) = -1` in the class (quadratic reciprocity: `(7/p) = (p/7)`). -/
theorem quadraticChar_seven (hC : InClass p) : χ (7 : ZMod p) = -1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [quadraticChar_neg_one_iff_not_isSquare]
  have h := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := p) (q := 7) hC.mod_four
    (by norm_num)
  rw [Nat.cast_ofNat] at h
  rw [h, ← ZMod.natCast_mod]
  unfold InClass at hC
  rcases hC.2 with h7 | h7 | h7 <;> rw [h7]
  exacts [not_isSquare_three_zmod_seven, not_isSquare_five_zmod_seven,
    not_isSquare_six_zmod_seven]

theorem seven_ne_zero (hC : InClass p) : (7 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((7 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat]; exact h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by norm_num)).mp h'
  exact hC.ne_seven this

/-- `d d̄ = 7` for `d = 75 - 53 r`, `d̄ = 75 + 53 r`, `r² = 2`. -/
theorem d_mul_dbar {r : ZMod p} (hr : r ^ 2 = 2) : (75 - 53 * r) * (75 + 53 * r) = (7 : ZMod p) := by
  linear_combination (-2809 : ZMod p) * hr

/-- **Proposition 1.6 (2).** The two point counts are `p + 1 ∓ 2c_p`, one of each sign. -/
theorem pointCount_pair (hC : InClass p) {r : ZMod p} (hr : r ^ 2 = 2) :
    ((pointCount p (-(75 - 53 * r) ^ 2) : ℤ) = p + 1 - 2 * cp p ∧
        (pointCount p (-(75 + 53 * r) ^ 2) : ℤ) = p + 1 + 2 * cp p) ∨
      ((pointCount p (-(75 - 53 * r) ^ 2) : ℤ) = p + 1 + 2 * cp p ∧
        (pointCount p (-(75 + 53 * r) ^ 2) : ℤ) = p + 1 - 2 * cp p) := by
  have hp2 := hC.ne_two
  obtain ⟨i, hi⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by have := hC.mod_four; omega)
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  have h7 := d_mul_dbar hr
  have hd : (75 - 53 * r : ZMod p) ≠ 0 := by
    intro h; rw [h, zero_mul] at h7; exact seven_ne_zero hC h7.symm
  have hdb : (75 + 53 * r : ZMod p) ≠ 0 := by
    intro h; rw [h, mul_zero] at h7; exact seven_ne_zero hC h7.symm
  have hsq : ∀ d : ZMod p, -d ^ 2 = (i * d) ^ 2 * 1 := fun d => by
    rw [mul_one, mul_pow, sq i, ← hi]; ring
  have hcount : ∀ d : ZMod p, d ≠ 0 →
      (pointCount p (-d ^ 2) : ℤ) = p + 1 + χ (i * d) * (2 * cp p) := by
    intro d hd0
    rw [pointCount_eq hp2, hsq, jac_sq_mul (mul_ne_zero hi0 hd0), jac_one_eq hp2]
  have hm1 : χ (-1) = 1 := by rw [hi, ← sq, quadraticChar_sq_one' hi0]
  have hprod : χ (i * (75 - 53 * r)) * χ (i * (75 + 53 * r)) = -1 := by
    rw [← map_mul, show i * (75 - 53 * r) * (i * (75 + 53 * r)) =
      (i * i) * ((75 - 53 * r) * (75 + 53 * r)) by ring, ← hi, h7, map_mul, hm1, one_mul,
      quadraticChar_seven hC]
  rw [hcount _ hd, hcount _ hdb]
  rcases quadraticChar_dichotomy (mul_ne_zero hi0 hd) with h | h
  · rw [h, one_mul] at hprod
    right; rw [h, hprod]; constructor <;> ring
  · rw [h] at hprod
    have : χ (i * (75 + 53 * r)) = 1 := by linarith
    left; rw [h, this]; constructor <;> ring

/-- **Proposition 1.6 (1).** `c_p` is odd. -/
theorem cp_odd (hC : InClass p) : cp p % 2 = 1 := by
  have : Fact (Nat.Prime p) := inferInstance
  obtain ⟨r, hr⟩ := (ZMod.exists_sq_eq_two_iff (p := p) hC.ne_two).mpr (Or.inl hC.1)
  have hr2 : r ^ 2 = 2 := by rw [sq, ← hr]
  have hd : (75 - 53 * r : ZMod p) ≠ 0 := by
    intro h; have h7 := d_mul_dbar hr2; rw [h, zero_mul] at h7; exact seven_ne_zero hC h7.symm
  have h4 := four_dvd_pointCount hC.ne_two hd
  have h4' : (4 : ℤ) ∣ (pointCount p (-(75 - 53 * r) ^ 2) : ℤ) := by exact_mod_cast h4
  have h8 := hC.1
  rcases pointCount_pair hC hr2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] at h4' <;> omega

/-- **Proposition 1.6 (1).** `p = c_p² + e_p²`, where `e_p = φ_p(r₀)/2` for any non-square `r₀`. -/
theorem sq_add_sq_of_nonsquare (hC : InClass p) {r₀ : ZMod p} (hr₀ : ¬ IsSquare r₀) :
    (p : ℤ) = cp p ^ 2 + (jac r₀ / 2) ^ 2 := by
  have hJ := jacobsthal hC.mod_four hr₀
  obtain ⟨k, hk⟩ := jac_even hC.ne_two r₀
  rw [jac_one_eq hC.ne_two, hk] at hJ
  have : (k + k) / 2 = k := by omega
  rw [hk, this]
  linarith

theorem exists_sq_add_sq (hC : InClass p) : ∃ e : ℤ, (p : ℤ) = cp p ^ 2 + e ^ 2 := by
  obtain ⟨r₀, hr₀⟩ := FiniteField.exists_nonsquare (ringChar_zmod_ne_two (p := p) hC.ne_two)
  exact ⟨_, sq_add_sq_of_nonsquare hC hr₀⟩

end

/-- **Proposition 1.6 (3).** The gcd of the two point counts is `4 gcd(c_p, p + 1)`. -/
theorem gcd_pointCount_eq {p : ℕ} (hp : p.Prime) (hC : InClass p) {r : ZMod p} (hr : r ^ 2 = 2) :
    Nat.gcd (pointCount p (-(75 - 53 * r) ^ 2)) (pointCount p (-(75 + 53 * r) ^ 2))
      = 4 * Int.gcd (cp p) (p + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  refine nat_gcd_eq_of_sub_add _ _ (cp p) (p + 1) (cp_odd hC) ?_ ?_
  · have := hC.1; omega
  · rcases pointCount_pair hC hr with h | h
    · exact Or.inl h
    · exact Or.inr h

/-- **Proposition 1.6 (4), "⇐".** A class prime with `gcd(c_p, p + 1) = 1` is a good slope
prime. -/
theorem goodSlopePrime_of_gcd {p : ℕ} (hp : p.Prime) (hC : InClass p)
    (h : Int.gcd (cp p) (p + 1) = 1) : GoodSlopePrime p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ := (ZMod.exists_sq_eq_two_iff (p := p) hC.ne_two).mpr (Or.inl hC.1)
  have hr2 : r ^ 2 = 2 := by rw [sq, ← hr]
  have h7 := d_mul_dbar hr2
  refine ⟨hp, r, hr2, ?_, ?_, ?_⟩
  · intro h0; rw [h0, zero_mul] at h7; exact seven_ne_zero hC h7.symm
  · intro h0; rw [h0, mul_zero] at h7; exact seven_ne_zero hC h7.symm
  · rw [gcd_pointCount_eq hp hC hr2, h]

/-- **Proposition 1.6 (4).** For a class prime, `GoodSlopePrime p ↔ gcd(c_p, p + 1) = 1`. -/
theorem goodSlopePrime_iff {p : ℕ} (hp : p.Prime) (hC : InClass p) :
    GoodSlopePrime p ↔ Int.gcd (cp p) (p + 1) = 1 := by
  refine ⟨fun hG => ?_, goodSlopePrime_of_gcd hp hC⟩
  obtain ⟨-, r, hr, -, -, hgcd⟩ := hG
  rw [gcd_pointCount_eq hp hC hr] at hgcd
  omega

/-- **Proposition 1.6 (4), second part.** An odd prime `ℓ` dividing `c_p` and `p + 1` satisfies
`ℓ ≡ 1 (mod 4)`. -/
theorem mod_four_of_dvd_cp {p ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hp : p.Prime) (hC : InClass p)
    (h1 : (ℓ : ℤ) ∣ cp p) (h2 : ℓ ∣ p + 1) : ℓ % 4 = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨e, he⟩ := exists_sq_add_sq hC
  have hc0 : ((cp p : ℤ) : ZMod ℓ) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h1
  have hp0 : ((p + 1 : ℕ) : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h2
  have he' : ((e : ℤ) : ZMod ℓ) ^ 2 = -1 := by
    have := congrArg (fun z : ℤ => (z : ZMod ℓ)) he
    push_cast at this hp0
    rw [hc0] at this
    linear_combination -this + hp0
  have h3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one he'
  have h2' : ℓ % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hℓ).mpr hℓ2
  omega

/-! ### Sanity check: `p = 17` -/

theorem inClass_seventeen : InClass 17 := by decide

theorem pointCount_seventeen_one : pointCount 17 (1 : ZMod 17) = 16 := by
  rw [pointCount_eq_card]; decide

theorem cp_seventeen : cp 17 = -1 := by
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have h16 := pointCount_seventeen_one
  have h := pointCount_eq (p := 17) (by norm_num) (1 : ZMod 17)
  rw [h16] at h
  rw [cp_eq]
  push_cast at h
  omega

/-- `GoodSlopePrime 17`, reproved from the description (`InClass 17`, `c_17 = -1`). -/
theorem goodSlopePrime_seventeen' : GoodSlopePrime 17 :=
  goodSlopePrime_of_gcd (by norm_num) inClass_seventeen (by rw [cp_seventeen]; decide)

end ZInQ.Density
