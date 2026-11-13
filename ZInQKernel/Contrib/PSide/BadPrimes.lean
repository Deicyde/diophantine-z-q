import ZInQKernel.RouteK.Rank.LFunctionCd

/-!
# P3: the point-count formula for `a_p(C_d)` at the primes `p ∣ 2d`

`LFunction_cd_apply_prime_eq_sub_card` (`RouteK/Rank/LFunctionCd.lean`) gives, for odd squarefree
`d` and `p ∤ 2d`, `a_p(C_d) = p − #{(x, y) ∈ 𝔽_p² : y² = x³ − d² x}`. At the bad primes `p ∣ 2d`
Mathlib's coefficient is `0` (`LFunction_cd_apply_prime_of_dvd`, additive reduction), and the
affine count is `p` there too:

* `p ∣ d`: the reduction is the cusp `y² = x³`, whose affine points are `(t², t³)`, `t ∈ 𝔽_p`
  (`natCard_cusp`);
* `p = 2`: `y² = x³ − x` over `𝔽₂` has the two points `(0, 0)`, `(1, 0)`.

So the formula holds at every prime (`LFunction_cd_apply_prime_eq_sub_card_all`).
-/

namespace ZInQ.Contrib.PSide

open ZInQ.Literature WeierstrassCurve

/-- The affine points of the cusp `y² = x³` over a field are `(t², t³)`. -/
def cuspEquiv (F : Type*) [Field F] : F ≃ {xy : F × F // xy.2 ^ 2 = xy.1 ^ 3} where
  toFun t := ⟨(t ^ 2, t ^ 3), by ring⟩
  invFun xy := xy.1.2 / xy.1.1
  left_inv t := by
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · field_simp
  right_inv := by
    rintro ⟨⟨x, y⟩, h⟩
    simp only at h
    rcases eq_or_ne x 0 with rfl | hx
    · have hy : y = 0 := by simpa using h
      subst hy; simp
    · refine Subtype.ext (Prod.ext ?_ ?_)
      · simp only [div_pow, h]; field_simp
      · simp only
        have : y ^ 3 = y * x ^ 3 := by rw [← h]; ring
        rw [div_pow, this]; field_simp

/-- `#{(x, y) ∈ F² : y² = x³} = #F`. -/
theorem natCard_cusp (F : Type*) [Field F] :
    Nat.card {xy : F × F // xy.2 ^ 2 = xy.1 ^ 3} = Nat.card F :=
  (Nat.card_congr (cuspEquiv F)).symm

/-- At `p ∣ d`, the affine count of `y² = x³ − d² x` over `𝔽_p` is `p`. -/
theorem natCard_cd_of_dvd {d p : ℕ} [Fact p.Prime] (hp : p ∣ d) :
    Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1} = p := by
  have h0 : (d : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff d p).mpr hp
  have e : ∀ xy : ZMod p × ZMod p,
      xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1 ↔ xy.2 ^ 2 = xy.1 ^ 3 := fun xy => by
    rw [h0]; ring_nf
  rw [Nat.card_congr (Equiv.subtypeEquivRight e), natCard_cusp, Nat.card_zmod]

/-- At `p = 2` (odd `d`), the affine count of `y² = x³ − d² x` over `𝔽₂` is `2`. -/
theorem natCard_cd_two {d : ℕ} (hd : Odd d) :
    Nat.card {xy : ZMod 2 × ZMod 2 // xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod 2) ^ 2 * xy.1} = 2 := by
  have h1 : (d : ZMod 2) = 1 := by
    obtain ⟨k, rfl⟩ := hd
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl]; simp
  rw [h1, Nat.card_eq_fintype_card]
  decide

/-- **P3: the point count at the bad primes**: for odd squarefree `d` and a prime `p ∣ 2d`,
`a_p(C_d) = 0 = p − #{(x, y) ∈ 𝔽_p² : y² = x³ − d² x}`. -/
theorem LFunction_cd_apply_prime_eq_sub_card_of_dvd {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    (p : ℕ) [hp' : Fact p.Prime] (hp : p ∣ 2 * d) :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction p =
      p - Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1} := by
  rw [LFunction_cd_apply_prime_of_dvd hd hsq p hp]
  rcases (Nat.Prime.dvd_mul hp'.out).mp hp with h2 | h2
  · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp'.out Nat.prime_two).mp h2
    subst hp2
    rw [natCard_cd_two hd]; simp
  · rw [natCard_cd_of_dvd h2]; simp

/-- **The point-count formula at every prime**: for odd squarefree `d` and every prime `p`,
the Dirichlet coefficient of Mathlib's `L(C_d, s)` at `p` is
`p − #{(x, y) ∈ 𝔽_p² : y² = x³ − d² x}`. -/
theorem LFunction_cd_apply_prime_eq_sub_card_all {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    (p : ℕ) [Fact p.Prime] :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction p =
      p - Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1} := by
  by_cases hp : p ∣ 2 * d
  · exact LFunction_cd_apply_prime_eq_sub_card_of_dvd hd hsq p hp
  · exact LFunction_cd_apply_prime_eq_sub_card hd hsq p hp

end ZInQ.Contrib.PSide
