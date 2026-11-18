import Mathlib

/-! Appendix F, tex 8274–8297: combine the two good-reduction bounds,
then clear the finite-character projection with the same multiplier. -/

namespace ZInQ.Manuscript.RC.Stages

/-- The manuscript's product of the four possible residue-field point counts. -/
def reductionBound (count : ℕ → ℕ) : ℕ :=
  ∏ f ∈ Finset.Icc 1 4, count f

theorem count_dvd_reductionBound (count : ℕ → ℕ) {f : ℕ} (h₁ : 1 ≤ f) (h₄ : f ≤ 4) :
    count f ∣ reductionBound count :=
  Finset.dvd_prod_of_mem count (Finset.mem_Icc.mpr ⟨h₁, h₄⟩)

/-- Tex 8280–8285. The local inputs are precisely the prime-to-p torsion bounds
from reduction, with the choice of residue degree already made. -/
theorem two_good_prime_bound {X : Type*} [AddCommGroup X] {p q B₁ B₂ : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h₁ : ∀ n : ℕ, ¬ p ∣ n → ∀ x : X, n • x = 0 → B₁ • x = 0)
    (h₂ : ∀ n : ℕ, ¬ q ∣ n → ∀ x : X, n • x = 0 → B₂ • x = 0)
    {x : X} (hx : IsOfFinAddOrder x) : (B₁ * B₂) • x = 0 := by
  let m := addOrderOf x
  have hm : m ≠ 0 := (addOrderOf_pos_iff.mpr hx).ne'
  let u := p ^ padicValNat p m
  let v := Nat.divMaxPow m p
  have huv : u * v = m := Nat.pow_padicValNat_mul_divMaxPow p m
  have huv₀ : u ≠ 0 ∧ v ≠ 0 := by
    constructor <;> intro h <;> simp [h] at huv <;> exact hm huv.symm
  have hpu : ¬ q ∣ u := by
    intro h
    have hd := hq.dvd_of_dvd_pow h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp hd).symm
  have hpv : ¬ p ∣ v := Nat.not_dvd_divMaxPow hp.one_lt hm
  have hx₁ : v • (u • x) = 0 := by
    rw [← mul_nsmul, huv]
    exact addOrderOf_nsmul_eq_zero x
  have hx₂ : u • (v • x) = 0 := by
    rw [← mul_nsmul', huv]
    exact addOrderOf_nsmul_eq_zero x
  have hB₁ := h₁ v hpv (u • x) hx₁
  have hB₂ := h₂ u hpu (v • x) hx₂
  have hvB : v ∣ B₁ := by
    rw [← mul_nsmul, ← addOrderOf_dvd_iff_nsmul_eq_zero] at hB₁
    change m ∣ u * B₁ at hB₁
    rw [← huv] at hB₁
    exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero huv₀.1)).mp hB₁
  have huB : u ∣ B₂ := by
    rw [← mul_nsmul, ← addOrderOf_dvd_iff_nsmul_eq_zero] at hB₂
    change m ∣ v * B₂ at hB₂
    rw [← huv, mul_comm u v] at hB₂
    exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero huv₀.2)).mp hB₂
  rw [← addOrderOf_dvd_iff_nsmul_eq_zero]
  change m ∣ B₁ * B₂
  rw [← huv, mul_comm B₁ B₂]
  exact Nat.mul_dvd_mul huB hvB

/-- Tex 8288–8297. If Y is the integral character projection of 4P, the
two-prime bound kills 4P-Y. Any further fixed factor preserves the character. -/
theorem multiplier_character {X : Type*} [AddCommGroup X] (B L₀ : ℕ) (P Y : X)
    (hkill : B • (4 • P - Y) = 0)
    (γ : X →+ X) (χ : ℤ) (hY : γ Y = χ • Y) :
    γ ((L₀ * (4 * B)) • P) = χ • ((L₀ * (4 * B)) • P) := by
  have h := sub_eq_zero.mp (by simpa only [nsmul_sub] using hkill)
  have he : (L₀ * (4 * B)) • P = L₀ • (B • Y) := by
    rw [mul_nsmul', mul_nsmul, h]
  rw [he, map_nsmul, map_nsmul, hY, smul_comm B χ, smul_comm L₀ χ]

#print axioms count_dvd_reductionBound
#print axioms two_good_prime_bound
#print axioms multiplier_character

end ZInQ.Manuscript.RC.Stages
