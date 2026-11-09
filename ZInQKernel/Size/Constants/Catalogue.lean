import ZInQKernel.Size.Constants.Small
import ZInQKernel.Size.Constants.Closed

/-!
# The catalogue below the progression cutoff, and the size of `N_s` and `ℓ`

Blueprint: `size/constants/catalogue-bounds.md`, `size/constants/catalogue-size.md`.

Under the catalogue bound CAT₈ every catalogue prime lies in `(324, X)` with `X = 2^(W⁸)`, so
`H_max < X` and `1 ≤ H_cat ≤ X^(22W) = 2^(22 W⁹)`. With `P_s < 2^433` and `W < 2^512` this gives
`N_s < 2^(2^4613)` and `ℓ < 2^(2^4623)`. Catalogue primes are indexed from `0`
(`Syntax.cataloguePrime W 324 r j` is the blueprint's `p_{r,j+1}`). Nothing is evaluated: the
estimates are proved for variables and applied to the named constants.
-/

namespace ZInQ.Size

open Syntax AmbientPow

/-! ### The catalogue below `X = 2^(W⁸)` -/

/-- Every catalogue prime lies strictly between `324` and `X = 2^(W⁸)`. -/
theorem cataloguePrime_bounds (hCAT : CatalogueBound8) {r j : ℕ} (hr1 : 1 ≤ r) (hr : r < W)
    (hcop : r.Coprime W) (hj : j < 22) :
    324 < Syntax.cataloguePrime W 324 r j ∧ Syntax.cataloguePrime W 324 r j < 2 ^ W ^ 8 := by
  rw [W_eq_catalogueModulus] at hr hcop ⊢
  refine ⟨lt_cataloguePrime (mem_unitResidues.2 ⟨hr1, hr, hcop⟩) j, ?_⟩
  rw [← Syntax.cataloguePrime_catalogueModulus]
  exact cataloguePrime_lt_of_catalogueBound8 hCAT hr hcop hj

/-- `1 ≤ H_cat ≤ X^(22W)`. -/
theorem Hcat_bounds (hCAT : CatalogueBound8) : 1 ≤ Hcat ∧ Hcat ≤ (2 ^ W ^ 8) ^ (22 * W) := by
  refine ⟨Hcat_pos, ?_⟩
  rw [Hcat_eq, catalogueProduct_eq_prod_catalogueFinset]
  have hcard : (catalogueFinset W 22 324).card ≤ 22 * W :=
    calc (catalogueFinset W 22 324).card ≤ (unitResidues W ×ˢ Finset.range 22).card :=
          Finset.card_image_le
      _ = (unitResidues W).card * 22 := by rw [Finset.card_product, Finset.card_range]
      _ ≤ W * 22 :=
          Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans (Finset.card_range W).le)
      _ = 22 * W := Nat.mul_comm _ _
  calc ∏ p ∈ catalogueFinset W 22 324, p ≤ (2 ^ W ^ 8) ^ (catalogueFinset W 22 324).card := by
        refine prod_le_natPow_card _ _ _ fun p hp => ?_
        obtain ⟨r, hr, j, hj, rfl⟩ := mem_catalogueFinset.1 hp
        obtain ⟨hr1, hrW, hcop⟩ := mem_unitResidues.1 hr
        exact (cataloguePrime_bounds hCAT hr1 hrW hcop hj).2.le
    _ ≤ (2 ^ W ^ 8) ^ (22 * W) := natPow_le_natPow_right (natPow_pos (by decide) _) hcard

/-- The catalogue below the progression cutoff (the blueprint statement). -/
theorem catalogue_bounds (hCAT : CatalogueBound8) :
    (∀ r j : ℕ, 1 ≤ r → r < W → r.Coprime W → j < 22 →
      324 < Syntax.cataloguePrime W 324 r j ∧ Syntax.cataloguePrime W 324 r j < 2 ^ W ^ 8) ∧
    Hmax < 2 ^ W ^ 8 ∧ 1 ≤ Hcat ∧ Hcat ≤ (2 ^ W ^ 8) ^ (22 * W) :=
  ⟨fun _ _ hr1 hr hcop hj => cataloguePrime_bounds hCAT hr1 hr hcop hj, Hmax_lt_of_catalogueBound8 hCAT,
    Hcat_bounds hCAT⟩

/-! ### Size of `N_s` and `ℓ` -/

set_option exponentiation.threshold 4700 in
/-- `W < 2^512` gives `W⁹ < 2^4608`. -/
theorem pow_nine_lt_of_lt {w : ℕ} (hw : w < 2 ^ 512) : w ^ 9 < 2 ^ 4608 :=
  calc w ^ 9 < (2 ^ 512) ^ 9 := natPow_lt_natPow_left hw (by decide)
    _ = 2 ^ (512 * 9) := (natPow_mul _ _ _).symm

theorem two_pow_pow_eight_pow_eq (w k : ℕ) :
    (2 ^ w ^ 8) ^ (k * w) = 2 ^ (k * w ^ 9) := by
  rw [← natPow_mul]; congr 1; ring

set_option exponentiation.threshold 4700 in
/-- The estimate for `N_s`, for variables. -/
theorem mul_lt_of_catalogue {p h w : ℕ} (hp : p < 2 ^ 433) (hw : w < 2 ^ 512)
    (hh : h ≤ (2 ^ w ^ 8) ^ (22 * w)) : p * h < 2 ^ 2 ^ 4613 := by
  rw [two_pow_pow_eight_pow_eq] at hh
  have he : 433 + 22 * w ^ 9 < 2 ^ 4613 :=
    calc 433 + 22 * w ^ 9 < 433 + 22 * 2 ^ 4608 :=
          Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left (pow_nine_lt_of_lt hw) (by decide)) _
      _ < 2 ^ 4613 := closed_comparisons_1.1
  calc p * h < 2 ^ 433 * 2 ^ (22 * w ^ 9) :=
        Nat.mul_lt_mul_of_lt_of_le hp hh (natPow_pos (by decide) _)
    _ = 2 ^ (433 + 22 * w ^ 9) := (natPow_add _ _ _).symm
    _ < 2 ^ 2 ^ 4613 := natPow_lt_natPow_right (by decide) he

set_option exponentiation.threshold 4700 in
/-- The estimate for `ℓ`, for variables. -/
theorem ell_lt_of_catalogue {p h w : ℕ} (hp : p < 2 ^ 433) (hw : w < 2 ^ 512)
    (hh : h ≤ (2 ^ w ^ 8) ^ (22 * w)) : 12 * (p ^ 2916 * h ^ 732) < 2 ^ 2 ^ 4623 := by
  rw [two_pow_pow_eight_pow_eq] at hh
  have hp' : p ^ 2916 < 2 ^ 1262628 :=
    calc p ^ 2916 < (2 ^ 433) ^ 2916 := natPow_lt_natPow_left hp (by decide)
      _ = 2 ^ (433 * 2916) := (natPow_mul _ _ _).symm
      _ = 2 ^ 1262628 := congrArg (2 ^ ·) closed_comparisons_1.2.2.1.symm
  have hh' : h ^ 732 ≤ 2 ^ (16104 * w ^ 9) :=
    calc h ^ 732 ≤ (2 ^ (22 * w ^ 9)) ^ 732 := natPow_le_natPow_left hh _
      _ = 2 ^ (16104 * w ^ 9) := by rw [← natPow_mul]; congr 1; ring
  have he : 4 + 1262628 + 16104 * w ^ 9 < 2 ^ 4623 :=
    calc 4 + 1262628 + 16104 * w ^ 9 < 4 + 1262628 + 16104 * 2 ^ 4608 :=
          Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left (pow_nine_lt_of_lt hw) (by decide)) _
      _ < 2 ^ 4623 := closed_comparisons_1.2.1
  calc 12 * (p ^ 2916 * h ^ 732) < 2 ^ 4 * (2 ^ 1262628 * 2 ^ (16104 * w ^ 9)) :=
        Nat.mul_lt_mul_of_lt_of_lt (by decide)
          (Nat.mul_lt_mul_of_lt_of_le hp' hh' (natPow_pos (by decide) _))
    _ = 2 ^ (4 + 1262628 + 16104 * w ^ 9) := by rw [natPow_add, natPow_add, Nat.mul_assoc]
    _ < 2 ^ 2 ^ 4623 := natPow_lt_natPow_right (by decide) he

/-- `1 ≤ N_s < 2^(2^4613)`. -/
theorem Ns_bounds (hCAT : CatalogueBound8) : 1 ≤ Ns ∧ Ns < 2 ^ 2 ^ 4613 := by
  refine ⟨Ns_pos, ?_⟩
  rw [Ns_eq]
  exact mul_lt_of_catalogue Ps_lt W_lt_two_pow_512 (Hcat_bounds hCAT).2

/-- `ℓ < 2^(2^4623)`. -/
theorem ell_lt (hCAT : CatalogueBound8) : ell < 2 ^ 2 ^ 4623 := by
  rw [ell_eq]
  exact ell_lt_of_catalogue Ps_lt W_lt_two_pow_512 (Hcat_bounds hCAT).2

/-- Size of `N_s` and `ℓ` (the blueprint statement). -/
theorem catalogue_size (hCAT : CatalogueBound8) :
    1 ≤ Ns ∧ Ns < 2 ^ 2 ^ 4613 ∧ ell < 2 ^ 2 ^ 4623 :=
  ⟨(Ns_bounds hCAT).1, (Ns_bounds hCAT).2, ell_lt hCAT⟩

end ZInQ.Size
