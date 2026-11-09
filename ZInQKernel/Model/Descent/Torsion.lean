import ZInQKernel.Model.Descent.Index
import ZInQKernel.Model.Descent.OddTorsion

/-!
# The torsion of `E(K₀)` is the full two-torsion

Blueprint: `model/descent/torsion.md`.

Every point of finite order in `E(K₀)` lies in `E(K₀)[2] = {O, (0,0), (d,0), (-d,0)}`, and
likewise for `C(K₀)`.

The proof splits the order. *Odd part*: a point of odd prime order is excluded by reduction at
`(17, s - 6)` and `(23, s - 5)` (`ZInQKernel/Model/Descent/OddTorsion.lean`). *Two-primary
part*: there is no point of order four, because a nonzero two-torsion point `T` is not in
`2E(K₀) = ker α` (the descent index): `α(T) ∈ {-1, d, -d}` is not a square class. The article
instead excludes order four by reduction (`8 ∤ 20`); the descent argument is shorter here.
-/

namespace ZInQ

open QuadraticAlgebra K0 Descent WeierstrassCurve WeierstrassCurve.Affine

theorem sqcInvariant_one : sqcInvariant 1 = (Multiplicative.ofAdd 0, ((1 : SignType), (1 : SignType))) :=
  map_one _

theorem sqcInvariant_neg_genD :
    sqcInvariant (sqc (-genD)) = (Multiplicative.ofAdd 1, ((-1 : SignType), (-1 : SignType))) := by
  rw [show -genD = -1 * genD by ring, sqc_mul (by norm_num) genD_ne_zero, map_mul,
    sqcInvariant_neg_one, sqcInvariant_genD]
  rfl

theorem sqc_neg_one_ne_one : sqc (-1 : K0) ≠ 1 := by
  intro h; have := congrArg sqcInvariant h
  rw [sqcInvariant_neg_one, sqcInvariant_one] at this
  revert this; decide

theorem sqc_genD_ne_one : sqc genD ≠ 1 := by
  intro h; have := congrArg sqcInvariant h
  rw [sqcInvariant_genD, sqcInvariant_one] at this
  revert this; decide

theorem sqc_neg_genD_ne_one : sqc (-genD) ≠ 1 := by
  intro h; have := congrArg sqcInvariant h
  rw [sqcInvariant_neg_genD, sqcInvariant_one] at this
  revert this; decide

/-- There is no point of order four in `E(K₀)`. -/
theorem two_nsmul_eq_zero_of_four_nsmul_eq_zero (P : genCurve.toAffine.Point) (h : 4 • P = 0) :
    2 • P = 0 := by
  have h2 : 2 • (2 • P) = 0 := by rw [← mul_nsmul']; exact h
  have hk : kummer (-genD ^ 2) (2 • P) = 1 := kummer_two_nsmul (b := -genD ^ 2) P
  rcases (genCurve_two_torsion (2 • P)).mp h2 with h0 | h0 | h0 | h0
  · exact h0
  · exact absurd (kummer_genT0.symm.trans ((congrArg (kummer (-genD ^ 2)) h0).symm.trans hk))
      sqc_neg_one_ne_one
  · exact absurd (kummer_genTd.symm.trans ((congrArg (kummer (-genD ^ 2)) h0).symm.trans hk))
      sqc_genD_ne_one
  · exact absurd (kummer_genTnegd.symm.trans ((congrArg (kummer (-genD ^ 2)) h0).symm.trans hk))
      sqc_neg_genD_ne_one

/-- **The torsion of `E(K₀)` is the two-torsion**: a point of finite order is killed by `2`. -/
theorem two_nsmul_eq_zero_of_isOfFinAddOrder {P : genCurve.toAffine.Point}
    (h : IsOfFinAddOrder P) : 2 • P = 0 := by
  set n := addOrderOf P with hn
  have hn0 : 0 < n := h.addOrderOf_pos
  have hnP : n • P = 0 := addOrderOf_nsmul_eq_zero P
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn0.ne'
  -- the odd part is trivial
  have hm1 : m = 1 := by
    by_contra hm1
    set q := m.minFac
    have hq : q.Prime := Nat.minFac_prime hm1
    have hqm : q ∣ m := Nat.minFac_dvd m
    have hq2 : q ≠ 2 := by
      rintro h2; rw [h2] at hqm; exact hm.not_two_dvd_nat hqm
    have hqn : q ∣ n := hnm ▸ dvd_mul_of_dvd_right hqm _
    have hQ : q • ((n / q) • P) = 0 := by
      rw [← mul_nsmul', Nat.mul_div_cancel' hqn, hnP]
    have := odd_prime_torsion_E q hq hq2 _ hQ
    have hdvd : n ∣ n / q := addOrderOf_dvd_of_nsmul_eq_zero this
    have hlt : n / q < n := Nat.div_lt_self hn0 hq.one_lt
    have hpos : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hn0 hqn) hq.pos
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)
  subst hm1
  rw [mul_one] at hnm
  -- the two-primary part has exponent at most two
  have ha : a ≤ 1 := by
    by_contra ha
    push Not at ha
    obtain ⟨k, rfl⟩ : ∃ k, a = k + 2 := ⟨a - 2, by omega⟩
    have h4 : 4 • (2 ^ k • P) = 0 := by
      rw [← mul_nsmul', show 4 * 2 ^ k = 2 ^ (k + 2) by ring, ← hnm, hnP]
    have h2 := two_nsmul_eq_zero_of_four_nsmul_eq_zero _ h4
    rw [← mul_nsmul'] at h2
    have hdvd : n ∣ 2 * 2 ^ k := addOrderOf_dvd_of_nsmul_eq_zero h2
    rw [hnm, show 2 * 2 ^ k = 2 ^ (k + 1) by ring] at hdvd
    have := Nat.le_of_dvd (by positivity) hdvd
    have := Nat.pow_lt_pow_right (show 1 < 2 by norm_num) (show k + 1 < k + 2 by omega)
    omega
  have hdvd : n ∣ 2 := by
    rw [hnm]; interval_cases a <;> norm_num
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mp hdvd

theorem isOfFinAddOrder_iff_two_nsmul_eq_zero (P : genCurve.toAffine.Point) :
    IsOfFinAddOrder P ↔ 2 • P = 0 :=
  ⟨two_nsmul_eq_zero_of_isOfFinAddOrder, fun h => isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    ⟨2, by norm_num, h⟩⟩

/-- The torsion subgroup of `E(K₀)` is `E(K₀)[2] = {O, (0,0), (d,0), (-d,0)}`. -/
theorem mem_torsion_E_iff (P : genCurve.toAffine.Point) :
    P ∈ AddCommGroup.torsion genCurve.toAffine.Point ↔
      P = 0 ∨ P = genT0 ∨ P = genTd ∨ P = genTnegd := by
  rw [AddCommGroup.mem_torsion, isOfFinAddOrder_iff_two_nsmul_eq_zero, genCurve_two_torsion]

/-- The torsion subgroup of `C(K₀)` is `C(K₀)[2] = {O, (0,0), (δ,0), (-δ,0)}`. -/
theorem two_nsmul_eq_zero_of_isOfFinAddOrder_C {Q : curveC.toAffine.Point}
    (h : IsOfFinAddOrder Q) : 2 • Q = 0 := by
  obtain ⟨n, hn, hQ⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp h
  have hP : IsOfFinAddOrder (theta.symm Q) :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, by rw [← map_nsmul, hQ, map_zero]⟩
  have := two_nsmul_eq_zero_of_isOfFinAddOrder hP
  rw [← theta.apply_symm_apply Q, two_nsmul_theta_eq_zero_iff]
  exact this

theorem mem_torsion_C_iff (Q : curveC.toAffine.Point) :
    Q ∈ AddCommGroup.torsion curveC.toAffine.Point ↔
      Q = 0 ∨ Q = cT0 ∨ Q = cTdelta ∨ Q = cTnegdelta := by
  rw [AddCommGroup.mem_torsion, ← curveC_two_torsion]
  exact ⟨two_nsmul_eq_zero_of_isOfFinAddOrder_C, fun h => isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    ⟨2, by norm_num, h⟩⟩

end ZInQ
