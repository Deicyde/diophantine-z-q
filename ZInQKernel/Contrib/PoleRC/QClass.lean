import ZInQKernel.Contrib.PoleRC.Recip

/-!
# Square classes at an odd prime `q`, for squarefree integers

`qcls q x = (v_q(x), [x q^{−v_q(x)} / q]) ∈ 𝔽₂ × 𝔽₂` for squarefree `x`: the class of `x` in
`ℚ_q*/ℚ_q*²` for odd `q` (valuation parity, Legendre symbol of the unit part).

* `lsym_mul`: `[xy/q] = [x/q] + [y/q]` for `x, y` prime to `q` (`legendreSym.mul`).
* `qcls_mul`: `qcls` is additive on products that are squarefree.
* `qcls_eq_sum`: for squarefree `x`, `qcls q x` is the sum of the classes of its prime factors and
  of its sign.
-/

namespace ZInQ.Manuscript.PoleRC

open Classical in
/-- The class of a squarefree integer `x` in `ℚ_q*/ℚ_q*²`, `q` odd: `(1, [(x/q)/q])` if `q ∣ x`,
`(0, [x/q])` otherwise. -/
noncomputable def qcls (q : ℕ) (x : ℤ) : ZMod 2 × ZMod 2 :=
  if (q : ℤ) ∣ x then (1, lsym (x / q) q) else (0, lsym x q)

theorem lsym_mul (q : ℕ) [Fact q.Prime] {x y : ℤ} (hx : (x : ZMod q) ≠ 0)
    (hy : (y : ZMod q) ≠ 0) : lsym (x * y) q = lsym x q + lsym y q := by
  have hxy : ((x * y : ℤ) : ZMod q) ≠ 0 := by push_cast; exact mul_ne_zero hx hy
  have key : ∀ z : ℤ, (z : ZMod q) ≠ 0 →
      (legendreSym q z = 1 ∧ lsym z q = 0) ∨ (legendreSym q z = -1 ∧ lsym z q = 1) := by
    intro z hz
    rcases legendreSym.eq_one_or_neg_one q hz with h | h
    · exact Or.inl ⟨h, lsym_of_isSquare ((legendreSym.eq_one_iff q hz).mp h)⟩
    · exact Or.inr ⟨h, lsym_of_not_isSquare ((legendreSym.eq_neg_one_iff q).mp h)⟩
  have hm := legendreSym.mul q x y
  rcases key x hx with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases key y hy with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    rcases key _ hxy with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;> rw [h1', h2', h3'] <;>
    rw [h1, h2, h3] at hm <;> first | decide | (norm_num at hm)

theorem intCast_ne_zero_of_not_dvd {q : ℕ} {x : ℤ} (h : ¬ (q : ℤ) ∣ x) : (x : ZMod q) ≠ 0 := by
  rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem not_dvd_div_of_squarefree {q : ℕ} (hq : q.Prime) {x : ℤ} (hx : Squarefree x)
    (h : (q : ℤ) ∣ x) : ¬ (q : ℤ) ∣ x / q := by
  intro h'
  obtain ⟨y, hy⟩ := h'
  have : (q : ℤ) * q ∣ x := ⟨y, by rw [← Int.ediv_mul_cancel h, hy]; ring⟩
  have := hx _ this
  rw [Int.isUnit_iff] at this
  rcases this with h1 | h1 <;> [exact hq.one_lt.ne' (by exact_mod_cast h1);
    exact absurd h1 (by have := hq.pos; omega)]

/-- **`qcls` is additive on squarefree products.** -/
theorem qcls_mul (q : ℕ) [hq : Fact q.Prime] {x y : ℤ} (hxy : Squarefree (x * y)) :
    qcls q (x * y) = qcls q x + qcls q y := by
  have hx : Squarefree x := Squarefree.of_mul_left hxy
  have hy : Squarefree y := Squarefree.of_mul_right hxy
  have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq.out
  unfold qcls
  by_cases h1 : (q : ℤ) ∣ x <;> by_cases h2 : (q : ℤ) ∣ y
  · exfalso
    have : (q : ℤ) * q ∣ x * y := mul_dvd_mul h1 h2
    have := hxy _ this
    exact hqp.not_unit this
  · have h3 : (q : ℤ) ∣ x * y := h1.mul_right y
    rw [if_pos h3, if_pos h1, if_neg h2]
    have : x * y / q = x / q * y := by
      rw [mul_comm x y, mul_comm (x / q) y, Int.mul_ediv_assoc _ h1]
    rw [this, lsym_mul q (intCast_ne_zero_of_not_dvd (not_dvd_div_of_squarefree hq.out hx h1))
      (intCast_ne_zero_of_not_dvd h2)]
    rfl
  · have h3 : (q : ℤ) ∣ x * y := h2.mul_left x
    rw [if_pos h3, if_neg h1, if_pos h2]
    have : x * y / q = x * (y / q) := Int.mul_ediv_assoc _ h2
    rw [this, lsym_mul q (intCast_ne_zero_of_not_dvd h1)
      (intCast_ne_zero_of_not_dvd (not_dvd_div_of_squarefree hq.out hy h2))]
    rfl
  · have h3 : ¬ (q : ℤ) ∣ x * y := fun h => (hqp.dvd_or_dvd h).elim h1 h2
    rw [if_neg h3, if_neg h1, if_neg h2,
      lsym_mul q (intCast_ne_zero_of_not_dvd h1) (intCast_ne_zero_of_not_dvd h2)]
    rfl

/-- `qcls q q = (1, 0)`. -/
theorem qcls_self (q : ℕ) [hq : Fact q.Prime] : qcls q q = (1, 0) := by
  unfold qcls
  rw [if_pos dvd_rfl, Int.ediv_self (by exact_mod_cast hq.out.ne_zero)]
  exact Prod.ext rfl (lsym_of_isSquare ⟨1, by simp⟩)

/-- `qcls q p = (0, [p/q])` for a prime `p ≠ q`. -/
theorem qcls_prime_ne (q p : ℕ) [hq : Fact q.Prime] (hp : p.Prime) (hpq : p ≠ q) :
    qcls q p = (0, lsym p q) := by
  unfold qcls
  rw [if_neg]
  intro h
  have : q ∣ p := by exact_mod_cast h
  exact hpq ((Nat.prime_dvd_prime_iff_eq hq.out hp).mp this).symm

/-- `qcls q (−1) = (0, s_q)`. -/
theorem qcls_neg_one (q : ℕ) [hq : Fact q.Prime] : qcls q (-1) = (0, lsym (-1) q) := by
  unfold qcls
  rw [if_neg]
  intro h
  have h1 : (q : ℤ) ∣ ((1 : ℕ) : ℤ) := by simpa using (dvd_neg.mp h)
  have := Int.natCast_dvd_natCast.mp h1
  exact hq.out.one_lt.ne' (Nat.dvd_one.mp this)

end ZInQ.Manuscript.PoleRC

namespace ZInQ.Manuscript.PoleRC

theorem qcls_one (q : ℕ) [hq : Fact q.Prime] : qcls q 1 = 0 := by
  have h := qcls_mul q (x := 1) (y := 1) (by simp)
  rw [mul_one] at h
  have : qcls q 1 + qcls q 1 = 0 := Prod.ext (zmod2_add_self _) (zmod2_add_self _)
  rw [← h] at this
  exact this

/-- `qcls` of a product of distinct primes dividing a squarefree `N`. -/
theorem qcls_prod (q : ℕ) [Fact q.Prime] (N : ℕ) (hN : Squarefree N) :
    ∀ T ⊆ N.primeFactors, qcls q (∏ p ∈ T, (p : ℤ)) = ∑ p ∈ T, qcls q p := by
  intro T
  induction T using Finset.induction_on with
  | empty => intro _; simp [qcls_one]
  | insert p T hpT ih =>
    intro hsub
    rw [Finset.prod_insert hpT, Finset.sum_insert hpT]
    have hsq : Squarefree ((p : ℤ) * ∏ p ∈ T, (p : ℤ)) := by
      have hdvd : (∏ p ∈ insert p T, p) ∣ N := by
        conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hN]
        exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
      rw [Finset.prod_insert hpT] at hdvd
      have : Squarefree (p * ∏ p ∈ T, p) := Squarefree.squarefree_of_dvd hdvd hN
      have h' : ((p * ∏ p ∈ T, p : ℕ) : ℤ) = (p : ℤ) * ∏ p ∈ T, (p : ℤ) := by push_cast; rfl
      rw [← h']
      exact Int.squarefree_natCast.mpr this
    rw [qcls_mul q hsq, ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))]

open Classical in
/-- **`qcls` of a squarefree integer**: the class of its sign plus the classes of its primes. -/
theorem qcls_eq_sum (q : ℕ) [Fact q.Prime] {x : ℤ} (hx : Squarefree x) :
    qcls q x = (if x < 0 then qcls q (-1) else 0) + ∑ p ∈ x.natAbs.primeFactors, qcls q p := by
  have hN : Squarefree x.natAbs := Int.squarefree_natAbs.mpr hx
  have hprod : (x.natAbs : ℤ) = ∏ p ∈ x.natAbs.primeFactors, (p : ℤ) := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hN]
    push_cast; rfl
  have habs := qcls_prod q x.natAbs hN _ (subset_refl _)
  rw [← hprod] at habs
  by_cases hneg : x < 0
  · rw [if_pos hneg]
    have hx' : x = -1 * (x.natAbs : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_neg hneg]; ring
    have hsq : Squarefree (-1 * (x.natAbs : ℤ)) := by rw [← hx']; exact hx
    conv_lhs => rw [hx']
    rw [qcls_mul q hsq, habs]
  · rw [if_neg hneg, zero_add]
    have hx' : x = (x.natAbs : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_nonneg (not_lt.mp hneg)]
    conv_lhs => rw [hx']
    rw [habs]

end ZInQ.Manuscript.PoleRC
