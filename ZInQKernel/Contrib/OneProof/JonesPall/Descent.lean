import ZInQKernel.Contrib.OneProof.JonesPall.Quaternion

/-!
# A prime norm in an integral quaternion annihilator

The descent adapts the genuine Lagrange/Euler descent in
`Mathlib.NumberTheory.SumFourSquares` (Chris Hughes, Apache 2.0, the project's
unchanged Mathlib pin). Unlike an arbitrary four-square descent, all operations
are on the LEFT and preserve the congruence `q * v = 0 (mod p)`.

No quaternion divisor theorem, local-global theorem, or ternary representation
is assumed. The initial element and all zero/divisibility cases are proved.
-/

namespace ZInQ.Contrib.OneProof.JonesPall

open scoped Quaternion

private def absNorm (q : Q) : ℕ :=
  q.re.natAbs ^ 2 + q.imI.natAbs ^ 2 + q.imJ.natAbs ^ 2 + q.imK.natAbs ^ 2

private theorem absNorm_cast (q : Q) : (absNorm q : ℤ) = Quaternion.normSq q := by
  simp only [absNorm, Nat.cast_add, Nat.cast_pow, Int.natCast_natAbs, sq_abs,
    Quaternion.normSq_def']

private theorem norm_pos {q : Q} (hq : q ≠ 0) : 0 < Quaternion.normSq q :=
  lt_of_le_of_ne Quaternion.normSq_nonneg (Ne.symm (Quaternion.normSq_ne_zero.mpr hq))

private theorem dvdQ_of_casts_zero {m : ℕ} {q : Q}
    (h0 : (q.re : ZMod m) = 0) (h1 : (q.imI : ZMod m) = 0)
    (h2 : (q.imJ : ZMod m) = 0) (h3 : (q.imK : ZMod m) = 0) : DvdQ m q :=
  ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h1,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h3⟩

private theorem balanced_difference {m : ℕ} [NeZero m] (q : Q) :
    let r : Q := ⟨(q.re : ZMod m).valMinAbs, (q.imI : ZMod m).valMinAbs,
      (q.imJ : ZMod m).valMinAbs, (q.imK : ZMod m).valMinAbs⟩
    DvdQ m (r - q) := by
  dsimp
  apply dvdQ_of_casts_zero <;>
    simp only [Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub,
      Quaternion.imK_sub, Int.cast_sub, ZMod.coe_valMinAbs, sub_self]

private theorem balanced_norm_dvd {m : ℕ} [NeZero m] (q : Q)
    (h : (m : ℤ) ∣ Quaternion.normSq q) :
    let r : Q := ⟨(q.re : ZMod m).valMinAbs, (q.imI : ZMod m).valMinAbs,
      (q.imJ : ZMod m).valMinAbs, (q.imK : ZMod m).valMinAbs⟩
    (m : ℤ) ∣ Quaternion.normSq r := by
  dsimp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h ⊢
  simpa only [Quaternion.normSq_def', Int.cast_add, Int.cast_pow,
    ZMod.coe_valMinAbs] using h

private theorem square_dvd_norm {m : ℤ} {q : Q} (h : DvdQ m q) :
    m ^ 2 ∣ Quaternion.normSq q :=
  ⟨Quaternion.normSq (divQ m q), (normSq_divQ h).symm⟩

/-- A nonzero residue with square and norm zero modulo an odd prime has an
integral quaternion of norm p in its left annihilator. -/
theorem exists_norm_prime_annihilator (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (v : Q) (hv : ¬ DvdQ p v) (hvv : DvdQ p (v * v))
    (hNv : (p : ℤ) ∣ Quaternion.normSq v) :
    ∃ q : Q, Quaternion.normSq q = (p : ℤ) ∧ DvdQ p (q * v) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hpge : 2 ≤ p := hp.two_le
  have hpI : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpodd : Odd p := (hp.eq_two_or_odd').resolve_left hp2
  have hpnot2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have hnat : p ∣ 2 := by exact_mod_cast h
    have := Nat.le_of_dvd (by decide : 0 < 2) hnat
    omega
  let r0 : Q := ⟨(v.re : ZMod p).valMinAbs, (v.imI : ZMod p).valMinAbs,
    (v.imJ : ZMod p).valMinAbs, (v.imK : ZMod p).valMinAbs⟩
  have hdiff0 : DvdQ p (r0 - v) := balanced_difference v
  have hI0 : DvdQ p (r0 * v) := by
    have h := dvdQ_add (dvdQ_mul_right hdiff0 v) hvv
    simpa only [sub_mul, sub_add_cancel] using h
  have hr0ne : r0 ≠ 0 := by
    intro hzero
    apply hv
    have h := hdiff0
    rw [hzero, zero_sub] at h
    exact ⟨dvd_neg.mp h.1, dvd_neg.mp h.2.1, dvd_neg.mp h.2.2.1, dvd_neg.mp h.2.2.2⟩
  have hr0pos : 0 < Quaternion.normSq r0 := norm_pos hr0ne
  have hr0dvd : (p : ℤ) ∣ Quaternion.normSq r0 := balanced_norm_dvd v hNv
  have balanced_lt : ∀ x : ℤ, 2 * (x : ZMod p).valMinAbs.natAbs < p := by
    intro x
    exact (mul_le_mul' le_rfl (x : ZMod p).natAbs_valMinAbs_le).trans_lt
      (Nat.mul_div_lt_iff_not_dvd.mpr hpodd.not_two_dvd_nat)
  obtain ⟨kI, hkI⟩ := hr0dvd
  have hkIpos : 0 < kI := by
    have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
    rw [hkI] at hr0pos
    exact pos_of_mul_pos_right hr0pos hpZ.le
  lift kI to ℕ using hkIpos.le with k hkcast
  have hkr0 : Quaternion.normSq r0 = (k : ℤ) * (p : ℤ) := by
    simpa only [mul_comm] using hkI
  have hkr0nat : absNorm r0 = k * p := by
    apply Int.natCast_inj.mp
    rw [absNorm_cast]
    push_cast
    exact hkr0
  have hkp : k < p :=
    Int.lt_of_sum_four_squares_eq_mul hkr0nat (balanced_lt _) (balanced_lt _)
      (balanced_lt _) (balanced_lt _)
  have hkpos : 0 < k := by exact_mod_cast hkIpos
  have initial : ∃ m : ℕ, m < p ∧ 0 < m ∧
      ∃ q : Q, Quaternion.normSq q = (m : ℤ) * (p : ℤ) ∧ DvdQ p (q * v) :=
    ⟨k, hkp, hkpos, r0, hkr0, hI0⟩
  rcases Nat.findX initial with ⟨m, ⟨hmp, hmpos, q, hNq, hIq⟩, hmin⟩
  rcases (Nat.one_le_iff_ne_zero.mpr hmpos.ne').eq_or_lt with hm1 | hmgt
  · subst m
    exact ⟨q, by simpa using hNq, hIq⟩
  exfalso
  have hmne : (m : ℤ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hpnotm : ¬ (p : ℤ) ∣ (m : ℤ) := by
    intro h
    have hnat : p ∣ m := by exact_mod_cast h
    have := Nat.le_of_dvd hmpos hnat
    omega
  by_cases hmeven : 2 ∣ m
  · obtain ⟨s, hs⟩ := hmeven
    have hspos : 0 < s := by omega
    have hsm : s < m := by omega
    have hNq2 : (2 : ℤ) ∣ Quaternion.normSq q := by
      rw [hNq, hs]
      push_cast
      exact dvd_mul_of_dvd_left (dvd_mul_right 2 (s : ℤ)) (p : ℤ)
    obtain ⟨a, hNa, hdiv⟩ := exists_halving_multiplier q hNq2
    let q' := divQ 2 (a * q)
    have hIq' : DvdQ p (q' * v) := divQ_preserves_annihilator hpI hpnot2 hIq hdiv
    have hNq' : Quaternion.normSq q' = (s : ℤ) * (p : ℤ) := by
      have h := normSq_divQ hdiv
      change (2 : ℤ) ^ 2 * Quaternion.normSq q' = Quaternion.normSq (a * q) at h
      rw [map_mul, hNa, hNq, hs] at h
      push_cast at h
      nlinarith
    exact hmin s hsm ⟨hsm.trans hmp, hspos, q', hNq', hIq'⟩
  · let : NeZero m := ⟨hmpos.ne'⟩
    let r : Q := ⟨(q.re : ZMod m).valMinAbs, (q.imI : ZMod m).valMinAbs,
      (q.imJ : ZMod m).valMinAbs, (q.imK : ZMod m).valMinAbs⟩
    have hdiff : DvdQ m (r - q) := balanced_difference q
    have hmNq : (m : ℤ) ∣ Quaternion.normSq q := by
      rw [hNq]
      exact dvd_mul_right _ _
    have hmNr : (m : ℤ) ∣ Quaternion.normSq r := balanced_norm_dvd q hmNq
    have habs : m ∣ absNorm r := by
      rw [← Int.natCast_dvd_natCast, absNorm_cast]
      exact hmNr
    obtain ⟨s, hs⟩ := habs
    have hNr : Quaternion.normSq r = (m : ℤ) * (s : ℤ) := by
      rw [← absNorm_cast, hs]
      push_cast
      rfl
    have hspos : 0 < s := by
      by_contra hs0
      have hs0 : s = 0 := by omega
      have hrzero : r = 0 := Quaternion.normSq_eq_zero.mp (by simpa [hs0] using hNr)
      have hmq : DvdQ m q := by
        have h := hdiff
        rw [hrzero, zero_sub] at h
        exact ⟨dvd_neg.mp h.1, dvd_neg.mp h.2.1, dvd_neg.mp h.2.2.1,
          dvd_neg.mp h.2.2.2⟩
      have hmd : (m : ℤ) ∣ (p : ℤ) := by
        have h := square_dvd_norm hmq
        rw [hNq, pow_two, mul_dvd_mul_iff_left hmne] at h
        exact h
      have hmnat : m ∣ p := by exact_mod_cast hmd
      exact (hp.eq_one_or_self_of_dvd m hmnat).elim (by omega) (by omega)
    have hflt : ∀ x : ℤ, 2 * (x : ZMod m).valMinAbs.natAbs < m := by
      intro x
      exact (mul_le_mul' le_rfl (x : ZMod m).natAbs_valMinAbs_le).trans_lt
        (Nat.mul_div_lt_iff_not_dvd.mpr hmeven)
    have hsm : s < m := by
      apply Int.lt_of_sum_four_squares_eq_mul (by simpa [absNorm, mul_comm] using hs)
      all_goals exact hflt _
    have hdiv : DvdQ m (star r * q) := by
      have h1 := dvdQ_mul_right (dvdQ_star hdiff) q
      rw [star_sub] at h1
      have h2 : DvdQ m (star q * q) := by
        rw [Quaternion.star_mul_self]
        exact dvdQ_coe hmNq
      have h := dvdQ_add h1 h2
      simpa only [sub_mul, sub_add_cancel] using h
    let q' := divQ m (star r * q)
    have hIq' : DvdQ p (q' * v) := divQ_preserves_annihilator hpI hpnotm hIq hdiv
    have hNq' : Quaternion.normSq q' = (s : ℤ) * (p : ℤ) := by
      have h := normSq_divQ hdiv
      change (m : ℤ) ^ 2 * Quaternion.normSq q' = Quaternion.normSq (star r * q) at h
      rw [map_mul, Quaternion.normSq_star, hNr, hNq] at h
      apply mul_left_cancel₀ (pow_ne_zero 2 hmne)
      calc
        (m : ℤ) ^ 2 * Quaternion.normSq q' = ((m : ℤ) * s) * ((m : ℤ) * p) := h
        _ = (m : ℤ) ^ 2 * ((s : ℤ) * p) := by ring
    exact hmin s hsm ⟨hsm.trans hmp, hspos, q', hNq', hIq'⟩

end ZInQ.Contrib.OneProof.JonesPall
