import ZInQKernel.Syntax.Constants.Relations
import ZInQKernel.Compiler.Precision.HeightConstant

/-!
# Prime sets and clearing exponents of the multiplication certificate

Blueprint: `multiplication/certificate/constants.md`.

The fixed constants `M₀`, `c_* = 4M₀`, `ℓ₀ = 12 P_s^2916 H_cat^732`, `R`, `A_ht` and `T` are the
syntax chapter's `Syntax.M0`, `Syntax.cstar`, `Syntax.ell`, `Syntax.R`, `Syntax.Aht`,
`Syntax.T`; none is evaluated. This file defines

* the prime sets `S_ht` (primes `≤ 324`), the catalogue `𝓗`, `S_b = S_ht ∪ 𝓗` and
  `S_mul = S_ht ∪ 𝓗 ∪ supp(c_*)`;
* the clearing exponents `B_p`, `C_p = 14 B_p`, `D_p = 51 C_p`, `E_p = 52 C_p + v_p(12) + 4`;
* the contact polynomial `F(t) = ∏_{c ∈ 𝒞} (t - c)` with `𝒞` the hypothesis file's
  `contactSet`, odd contact primes, and the test precisions `k_j`.

`M_S(t)` is the hypothesis file's `contactSupport S t`, so the six-contact estimate applies
verbatim.
-/

namespace ZInQ.Mult

open scoped BigOperators

/-! ### Prime sets -/

/-- `S_ht = {p prime : p ≤ 324}`. -/
def S_ht : Finset ℕ := Compiler.Precision.heightPrimes

/-- The fixed prime catalogue `𝓗`: the first twenty-two primes greater than `324` in each unit
class modulo `W = 4 P_s`. -/
noncomputable def catalogue : Finset ℕ := Syntax.catalogueFinset catalogueModulus 22 324

/-- `S_b = S_ht ∪ 𝓗`, the old primes cleared by `ℓ₀`. -/
noncomputable def S_b : Finset ℕ := S_ht ∪ catalogue

/-- `S_mul = S_ht ∪ 𝓗 ∪ {p prime : p ∣ c_*}`. -/
noncomputable def S_mul : Finset ℕ := S_ht ∪ catalogue ∪ Syntax.cstar.primeFactors

theorem mem_S_ht {p : ℕ} : p ∈ S_ht ↔ p.Prime ∧ p ≤ 324 := Compiler.Precision.mem_heightPrimes

theorem catalogue_eq : catalogue = Syntax.catalogueFinset catalogueModulus 22 324 := rfl

theorem coe_catalogue : (catalogue : Set ℕ) = catalogueSet := Syntax.catalogueSet_eq.symm

theorem mem_catalogue {p : ℕ} : p ∈ catalogue ↔ p ∈ catalogueSet := by
  rw [← coe_catalogue, Finset.mem_coe]

theorem mem_S_b {p : ℕ} : p ∈ S_b ↔ p ∈ S_ht ∨ p ∈ catalogue := Finset.mem_union

theorem mem_S_mul {p : ℕ} :
    p ∈ S_mul ↔ p ∈ S_ht ∨ p ∈ catalogue ∨ (p.Prime ∧ p ∣ Syntax.cstar ∧ Syntax.cstar ≠ 0) := by
  simp only [S_mul, Finset.mem_union, Nat.mem_primeFactors, or_assoc]

theorem S_b_subset_S_mul : S_b ⊆ S_mul := Finset.subset_union_left

/- The catalogue is never evaluated: elaborating a membership `p ∈ catalogue` as a term would
otherwise unfold it down to `range (4 · 324#)`. From here on the sets are used through
`mem_catalogue`, `coe_catalogue`, `mem_S_b` and `mem_S_mul` only. -/
attribute [irreducible] catalogue S_b S_mul

/-! ### Clearing exponents -/

/-- `B_p = 4` for `p ∈ S_ht` and `B_p = 1` otherwise (in particular for `p ∈ 𝓗`). -/
def Bp (p : ℕ) : ℕ := if p ∈ S_ht then 4 else 1

/-- `C_p = 14 B_p`. -/
def Cp (p : ℕ) : ℕ := 14 * Bp p

/-- `D_p = 51 C_p`. -/
def Dp (p : ℕ) : ℕ := 51 * Cp p

/-- `E_p = 52 C_p + v_p(12) + 4`. -/
def Ep (p : ℕ) : ℕ := 52 * Cp p + padicValNat p 12 + 4

/-! ### Contact values and test precisions -/

/-- `F(t) = t(t + 15)(t + 20)(t + 24)(t + 30)(t + 60)`. -/
def contactPoly (t : ℚ) : ℚ := t * (t + 15) * (t + 20) * (t + 24) * (t + 30) * (t + 60)

/-- A prime `p` is an odd contact prime of `t` if `v_p(t - c)` is positive and odd for some
`c ∈ 𝒞`. -/
def IsOddContactPrime (t : ℚ) (p : ℕ) : Prop :=
  p.Prime ∧ ∃ c ∈ contactSet, 0 < padicValRat p (t - c) ∧ Odd (padicValRat p (t - c))

/-- The test precisions `k_j = 1` for `j ≤ 8` and `k_j = 25` for `9 ≤ j ≤ 12` (indices from `0`
here: `k_j = 1` for `j < 8`). -/
def prec (j : Fin 12) : ℕ := if j.val < 8 then 1 else 25

/-! ### Elementary facts about the definitions -/

/-- `F(t) = ∏_{c ∈ 𝒞} (t - c)`. -/
theorem contactPoly_eq_prod (t : ℚ) : contactPoly t = ∏ c ∈ contactSet, (t - c) := by
  simp only [contactPoly, contactSet]
  rw [Finset.prod_insert (by norm_num), Finset.prod_insert (by norm_num),
    Finset.prod_insert (by norm_num), Finset.prod_insert (by norm_num),
    Finset.prod_insert (by norm_num), Finset.prod_singleton]
  ring

/-- `F(t) = 0` exactly when `t ∈ 𝒞`. -/
theorem contactPoly_eq_zero_iff (t : ℚ) : contactPoly t = 0 ↔ t ∈ contactSet := by
  rw [contactPoly_eq_prod, Finset.prod_eq_zero_iff]
  exact ⟨fun ⟨c, hc, h⟩ => sub_eq_zero.1 h ▸ hc, fun h => ⟨t, h, sub_self t⟩⟩

theorem contactPoly_ne_zero {t : ℚ} (ht : t ∉ contactSet) : contactPoly t ≠ 0 :=
  fun h => ht ((contactPoly_eq_zero_iff t).1 h)

/-- For `t ∉ 𝒞`, a prime divides `M_S(t)` exactly when it is an odd contact prime of `t`
outside `S`. -/
theorem prime_dvd_contactSupport_iff' {S : Finset ℕ} {t : ℚ} (ht : t ∉ contactSet) {p : ℕ}
    (hp : p.Prime) : p ∣ contactSupport S t ↔ p ∉ S ∧ IsOddContactPrime t p := by
  rw [prime_dvd_contactSupport_iff ht hp, IsOddContactPrime]
  exact and_congr_right fun _ => ⟨fun h => ⟨hp, h⟩, fun h => h.2⟩

theorem prec_of_lt {j : Fin 12} (hj : j.val < 8) : prec j = 1 := ite_eq_left hj

theorem prec_of_ge {j : Fin 12} (hj : 8 ≤ j.val) : prec j = 25 := ite_eq_right (by omega)

theorem Bp_of_mem_S_ht {p : ℕ} (hp : p ∈ S_ht) : Bp p = 4 := ite_eq_left hp

theorem Bp_of_not_mem_S_ht {p : ℕ} (hp : p ∉ S_ht) : Bp p = 1 := ite_eq_right hp

end ZInQ.Mult
