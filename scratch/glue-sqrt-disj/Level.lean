import Mathlib

namespace GlueSqrtDisj

/-- `p` is a unit mod `p^n - 1` (`n ≥ 1`). -/
theorem coprime_pow_sub_one {p : ℕ} (hp : 2 ≤ p) {n : ℕ} (hn : 0 < n) : p.Coprime (p ^ n - 1) := by
  have h1 : 1 ≤ p ^ n := Nat.one_le_pow _ _ (by omega)
  have hd : Nat.gcd p (p ^ n - 1) ∣ p ^ n := (Nat.gcd_dvd_left _ _).trans (dvd_pow_self p hn.ne')
  have hd' : Nat.gcd p (p ^ n - 1) ∣ p ^ n - 1 := Nat.gcd_dvd_right _ _
  have := Nat.dvd_sub hd hd'
  rwa [Nat.sub_sub_self h1, Nat.dvd_one] at this

/-- **Level change.** The order of `p` modulo `p^n - 1` is `n` (for `p ≥ 2`, `n ≥ 1`). -/
theorem orderOf_unit_pow_sub_one {p : ℕ} (hp : 2 ≤ p) {n : ℕ} (hn : 0 < n) :
    orderOf (ZMod.unitOfCoprime p (coprime_pow_sub_one hp hn)) = n := by
  have h1 : 1 ≤ p ^ n := Nat.one_le_pow _ _ (by omega)
  have key : ∀ d, ((ZMod.unitOfCoprime p (coprime_pow_sub_one hp hn)) ^ d = 1 ↔
      p ^ n - 1 ∣ p ^ d - 1) := by
    intro d
    have hd1 : 1 ≤ p ^ d := Nat.one_le_pow _ _ (by omega)
    rw [Units.ext_iff, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one,
      ← Nat.cast_pow, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub hd1, sub_eq_zero, Nat.cast_one,
      Nat.cast_pow]
  rw [orderOf_eq_iff hn]
  refine ⟨(key n).mpr dvd_rfl, fun d hdn hd0 h => ?_⟩
  have hdvd := (key d).mp h
  have hlt : p ^ d < p ^ n := Nat.pow_lt_pow_right (by omega) hdn
  have hpos : 0 < p ^ d - 1 := by
    have : p ≤ p ^ d := Nat.le_self_pow hd0.ne' p
    omega
  have := Nat.le_of_dvd hpos hdvd
  omega

/-- If `f = ord_m(p)` then `m ∣ p^f - 1`, hence `m ∣ p^(2f) - 1`. -/
theorem dvd_pow_orderOf_sub_one {p m : ℕ} (hcop : p.Coprime m) (t : ℕ) :
    m ∣ p ^ (t * orderOf (ZMod.unitOfCoprime p hcop)) - 1 := by
  have h := pow_orderOf_eq_one (ZMod.unitOfCoprime p hcop)
  have h' : (ZMod.unitOfCoprime p hcop) ^ (t * orderOf (ZMod.unitOfCoprime p hcop)) = 1 := by
    rw [mul_comm, pow_mul, h, one_pow]
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · have : m = 1 := by simpa using hcop
    subst this; exact one_dvd _
  have hd1 : 1 ≤ p ^ (t * orderOf (ZMod.unitOfCoprime p hcop)) := Nat.one_le_pow _ _ hp0
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one,
    ← Nat.cast_pow] at h'
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hd1, sub_eq_zero, Nat.cast_one]
  exact h'

end GlueSqrtDisj

#print axioms GlueSqrtDisj.orderOf_unit_pow_sub_one
#print axioms GlueSqrtDisj.dvd_pow_orderOf_sub_one
