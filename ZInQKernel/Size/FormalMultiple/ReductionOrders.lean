import ZInQKernel.Size.FormalMultiple.BadPlace
import ZInQKernel.Size.FormalMultiple.PointCount
import ZInQKernel.Multiplication.Local.PrimesAbove

/-!
# Reduction orders of `P₀`

Blueprint: `size/formal-multiple/reduction-orders.md`.

For every `N ≥ 1` there is `m₀` with `1 ≤ m₀ ≤ N⁶` such that `[m₀]P₀ ∈ E₁(π)` for every prime
`π` of `ℤ[s]` above an odd prime divisor `p` of `N` (`exists_reduction_multiple`).

* At a single prime `π ∤ 2` with finite residue field `k_π = ℤ[s]/(π)`, the reduction of `P₀`
  lies in the nonsingular group (at `(d)` by `genP0_mem_E0_d`, elsewhere by good reduction), so
  its order `n_π` satisfies `1 ≤ n_π ≤ 2 |k_π| + 1` and `[m n_π] P₀ ∈ E₁(π)`
  (`exists_order_at_prime`).
* Above an odd prime `p` there are two primes with `p` residues or one with `p²`
  (`primeR_split`, `primeP_inert`), so the product of the `n_π` is at most
  `(2 p + 1)² ≤ p⁶` or `2 p² + 1 ≤ p⁶` (`exists_order_at_odd_prime`).
* `m₀` is the product over the odd prime divisors of `N`, and `∏_{p ∣ N} p⁶ ≤ N⁶`.

Membership in `E₁(π)` depends only on the ideal `(π)` (`inE1_congr`), so the statement is over
all prime elements `π ∣ p`.
-/

namespace ZInQ.Size

open WeierstrassCurve WeierstrassCurve.Affine

/-- `E₁(π)` depends only on the ideal `(π)`. -/
theorem inE1_congr {π π' : Zs} (h : Associated π π') {A : K0}
    (Q : (shortCurve A).toAffine.Point) : InE1 π A Q ↔ InE1 π' A Q := by
  rcases Q with _ | ⟨x, y, hQ⟩
  · exact Iff.rfl
  · simp only [inE1_some_iff, VGe, vp_eq_of_associated h]

theorem mem_E1sub_congr {π π' : Zs} (hπ : Prime π) (hπ' : Prime π') (h : Associated π π')
    {A : K0} (hA : VGe π 0 A) (hA' : VGe π' 0 A) (Q : (shortCurve A).toAffine.Point) :
    Q ∈ E1sub hπ hA ↔ Q ∈ E1sub hπ' hA' := inE1_congr h Q

/-- The order of the reduction of a point of `E₀(π)` over a finite residue field. -/
theorem exists_order_of_mem_E0 {k : Type*} [Field k] [DecidableEq k] [Finite k] {π : Zs}
    (hπ : Prime π) (ρ : Zs →+* k) (hρ : ∀ a, ρ a = 0 ↔ π ∣ a) {A : K0} (hA : VGe π 0 A)
    {Ab : k} (hAb : resK π ρ A = Ab) (h2 : ¬π ∣ 2) {Q : (shortCurve A).toAffine.Point}
    (hQ : Q ∈ E0sub hπ ρ hρ hA hAb h2) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 2 * Nat.card k + 1 ∧ ∀ m : ℤ, (m * n : ℤ) • Q ∈ E1sub hπ hA := by
  have := Fintype.ofFinite k
  refine ⟨addOrderOf (redK π ρ A Ab Q), addOrderOf_pos _,
    addOrderOf_le_two_natCard_add_one Ab _, zsmul_addOrderOf_mem_E1 hπ ρ hρ hA hAb h2 hQ⟩

theorem span_isMaximal {π : Zs} (hπ : Prime π) : (Ideal.span {π}).IsMaximal :=
  ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal (by simpa using hπ.ne_zero)

theorem natCard_quot_genDZ : Nat.card (Zs ⧸ Ideal.span {genDZ}) = 7 := by
  rw [Nat.card_congr quotGenDEquiv.toEquiv, Nat.card_zmod]

/-- **The order at one prime.** For a prime `π ∤ 2` with finite residue field, the reduction of
`P₀` at `π` has an order `n` with `1 ≤ n ≤ 2 |ℤ[s]/(π)| + 1`, and `[m n] P₀ ∈ E₁(π)` for all
`m`. -/
theorem exists_order_at_prime {π : Zs} (hπ : Prime π) (h2 : ¬π ∣ 2)
    (hfin : Nat.card (Zs ⧸ Ideal.span {π}) ≠ 0) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 2 * Nat.card (Zs ⧸ Ideal.span {π}) + 1 ∧
      ∀ m : ℤ, (m * n : ℤ) • genP0 ∈ E1sub hπ (vge_neg_genD_sq _ hπ) := by
  by_cases hd : Associated π genDZ
  · -- the bad place: reduce with `residueSeven` at `d` and transfer
    obtain ⟨n, hn1, hn, hm⟩ := exists_order_of_mem_E0 prime_genDZ residueSeven residueSeven_ker
      (vge_neg_genD_sq _ prime_genDZ) resK_genA_d not_genDZ_dvd_two genP0_mem_E0_d
    have hspan : Ideal.span {π} = Ideal.span {genDZ} :=
      Ideal.span_singleton_eq_span_singleton.mpr hd
    refine ⟨n, hn1, ?_, fun m => ?_⟩
    · rw [hspan, natCard_quot_genDZ]; rwa [Nat.card_zmod] at hn
    · exact (mem_E1sub_congr hπ prime_genDZ hd (vge_neg_genD_sq _ hπ) (vge_neg_genD_sq _ prime_genDZ) _).mpr (hm m)
  · -- good reduction: the residue field `ℤ[s]/(π)`
    have := span_isMaximal hπ
    let _ : Field (Zs ⧸ Ideal.span {π}) := Ideal.Quotient.field _
    have : Finite (Zs ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero hfin
    classical
    have hρ := quotient_mk_eq_zero_iff π
    have hQ : genP0 ∈ E0sub hπ (Ideal.Quotient.mk (Ideal.span {π})) hρ (vge_neg_genD_sq _ hπ) rfl h2 := by
      rw [E0_eq_top_of_ne_d hπ _ hρ h2 hd]; exact AddSubgroup.mem_top _
    exact exists_order_of_mem_E0 hπ _ hρ (vge_neg_genD_sq _ hπ) rfl h2 hQ

/-- A prime above an odd prime does not divide `2`. -/
theorem not_dvd_two_of_dvd_odd {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {π : Zs}
    (hπ : Prime π) (hπp : π ∣ (p : Zs)) : ¬π ∣ 2 := by
  intro h2
  have hcop : IsCoprime (p : ℤ) 2 := by
    refine (Nat.prime_iff_prime_int.mp hp.out).irreducible.coprime_iff_not_dvd.mpr ?_
    intro hd
    have : (p : ℤ) ∣ 2 := hd
    have h := Int.le_of_dvd (by norm_num) this
    have h' := hp.out.two_le
    have : p = 2 := by omega
    exact hp2 this
  have hcop' : IsCoprime (p : Zs) 2 := by
    have := hcop.map (Int.castRingHom Zs); simpa using this
  exact hπ.not_isUnit (hcop'.isUnit_of_dvd' hπp h2)

/-- A generator of a prime ideal containing `p`. -/
theorem exists_generator {P : Ideal Zs} (hP : P.IsPrime) {p : ℕ} [hp : Fact p.Prime]
    (hpP : (p : Zs) ∈ P) : ∃ π : Zs, Prime π ∧ Ideal.span {π} = P ∧ π ∣ (p : Zs) := by
  refine ⟨Submodule.IsPrincipal.generator P, ?_, Ideal.span_singleton_generator P, ?_⟩
  · have hne : Submodule.IsPrincipal.generator P ≠ 0 := by
      rw [ne_eq, ← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero]
      rintro rfl
      have : (p : Zs) = 0 := (Submodule.mem_bot _).mp hpP
      have := congrArg QuadraticAlgebra.re this
      simp at this; exact hp.out.ne_zero this
    rw [← Ideal.span_singleton_prime hne, Ideal.span_singleton_generator]; exact hP
  · rw [← Ideal.mem_span_singleton, Ideal.span_singleton_generator]; exact hpP

/-- **The order above an odd prime.** For an odd prime `p` there is `n` with `1 ≤ n ≤ p⁶` and
`[m n] P₀ ∈ E₁(π)` for all `m` and every prime `π ∣ p`. -/
theorem exists_order_at_odd_prime {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ p ^ 6 ∧ ∀ π : Zs, ∀ hπ : Prime π, π ∣ (p : Zs) →
      ∀ m : ℤ, (m * n : ℤ) • genP0 ∈ E1sub hπ (vge_neg_genD_sq _ hπ) := by
  have h3 : 3 ≤ p := by
    have := hp.out.two_le
    rcases (show p = 2 ∨ 3 ≤ p by omega) with h | h
    · exact absurd h hp2
    · exact h
  obtain ⟨hb1, hb2⟩ := odd_prime_count_bounds h3
  by_cases hsq : IsSquare (2 : ZMod p)
  · -- split: two primes with `p` residues
    obtain ⟨r₀, hr₀⟩ := hsq
    set r : ℤ := (r₀.val : ℤ)
    have hr : (r : ZMod p) ^ 2 = 2 := by
      simp only [r, Int.cast_natCast, ZMod.natCast_zmod_val, sq]; exact hr₀.symm
    obtain ⟨hP₁, hP₂, -, hprod, -, hall⟩ := Mult.primeR_split hp2 hr
    have hpP₁ : (p : Zs) ∈ Mult.primeR p r := Ideal.subset_span (by simp)
    have hpP₂ : (p : Zs) ∈ Mult.primeR p (-r) := Ideal.subset_span (by simp)
    obtain ⟨π₁, hπ₁, hs₁, hd₁⟩ := exists_generator hP₁ hpP₁
    obtain ⟨π₂, hπ₂, hs₂, hd₂⟩ := exists_generator hP₂ hpP₂
    have hc₁ : Nat.card (Zs ⧸ Ideal.span {π₁}) = p := by
      rw [hs₁, Nat.card_congr (Mult.quotPrimeREquiv hr).toEquiv, Nat.card_zmod]
    have hc₂ : Nat.card (Zs ⧸ Ideal.span {π₂}) = p := by
      rw [hs₂, Nat.card_congr (Mult.quotPrimeREquiv (Mult.neg_sq_eq hr)).toEquiv, Nat.card_zmod]
    obtain ⟨n₁, hn₁, hle₁, hm₁⟩ := exists_order_at_prime hπ₁ (not_dvd_two_of_dvd_odd hp2 hπ₁ hd₁)
      (by rw [hc₁]; exact hp.out.ne_zero)
    obtain ⟨n₂, hn₂, hle₂, hm₂⟩ := exists_order_at_prime hπ₂ (not_dvd_two_of_dvd_odd hp2 hπ₂ hd₂)
      (by rw [hc₂]; exact hp.out.ne_zero)
    rw [hc₁] at hle₁
    rw [hc₂] at hle₂
    refine ⟨n₁ * n₂, Nat.one_le_iff_ne_zero.mpr (by positivity), ?_, ?_⟩
    · calc n₁ * n₂ ≤ (2 * p + 1) * (2 * p + 1) := Nat.mul_le_mul hle₁ hle₂
        _ = (2 * p + 1) ^ 2 := by ring
        _ ≤ p ^ 6 := hb2
    · intro π hπ hπp m
      have hP : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
      rcases hall _ hP (Ideal.mem_span_singleton.mpr hπp) with h | h
      · have hassoc : Associated π π₁ :=
          Ideal.span_singleton_eq_span_singleton.mp (h.trans hs₁.symm)
        refine (mem_E1sub_congr hπ hπ₁ hassoc (vge_neg_genD_sq _ hπ) (vge_neg_genD_sq _ hπ₁) _).mpr ?_
        have e : (m * ((n₁ * n₂ : ℕ) : ℤ)) = m * n₂ * n₁ := by push_cast; ring
        rw [e]; exact hm₁ (m * n₂)
      · have hassoc : Associated π π₂ :=
          Ideal.span_singleton_eq_span_singleton.mp (h.trans hs₂.symm)
        refine (mem_E1sub_congr hπ hπ₂ hassoc (vge_neg_genD_sq _ hπ) (vge_neg_genD_sq _ hπ₂) _).mpr ?_
        have e : (m * ((n₁ * n₂ : ℕ) : ℤ)) = m * n₁ * n₂ := by push_cast; ring
        rw [e]; exact hm₂ (m * n₁)
  · -- inert: one prime with `p²` residues
    obtain ⟨-, hcard, -, -⟩ := Mult.primeP_inert hsq
    have hπ₁ := Mult.prime_natCast_of_not_isSquare hsq
    obtain ⟨n₁, hn₁, hle₁, hm₁⟩ := exists_order_at_prime hπ₁
      (not_dvd_two_of_dvd_odd hp2 hπ₁ dvd_rfl) (by rw [hcard]; positivity)
    rw [hcard] at hle₁
    refine ⟨n₁, hn₁, hle₁.trans hb1, fun π hπ hπp m => ?_⟩
    have hassoc : Associated π (p : Zs) := hπ.associated_of_dvd hπ₁ hπp
    exact (mem_E1sub_congr hπ hπ₁ hassoc (vge_neg_genD_sq _ hπ) (vge_neg_genD_sq _ hπ₁) _).mpr (hm₁ m)

open Classical in
/-- The order chosen above an odd prime `p` (`1` for other `p`). -/
noncomputable def orderAbove (p : ℕ) : ℕ :=
  if h : p.Prime ∧ p ≠ 2 then
    have := Fact.mk h.1
    Classical.choose (exists_order_at_odd_prime h.2)
  else 1

theorem orderAbove_spec {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    1 ≤ orderAbove p ∧ orderAbove p ≤ p ^ 6 ∧ ∀ π : Zs, ∀ hπ : Prime π, π ∣ (p : Zs) →
      ∀ m : ℤ, (m * orderAbove p : ℤ) • genP0 ∈ E1sub hπ (vge_neg_genD_sq _ hπ) := by
  have := Fact.mk hp
  unfold orderAbove
  split_ifs with h
  · exact Classical.choose_spec (exists_order_at_odd_prime hp2)
  · exact absurd ⟨hp, hp2⟩ h

theorem orderAbove_pos (p : ℕ) : 1 ≤ orderAbove p := by
  by_cases h : p.Prime ∧ p ≠ 2
  · exact (orderAbove_spec h.1 h.2).1
  · simp [orderAbove, h]

theorem orderAbove_le {p : ℕ} (hp : p.Prime) : orderAbove p ≤ p ^ 6 := by
  by_cases h2 : p = 2
  · subst h2; simp [orderAbove]
  · exact (orderAbove_spec hp h2).2.1

/-- **Reduction orders of `P₀`.** For every `N ≥ 1` there is `m₀` with `1 ≤ m₀ ≤ N⁶` such
that for every odd prime `p ∣ N` and every prime `π` of `ℤ[s]` with `π ∣ p`,
`[m₀] P₀ ∈ E₁(π)`, i.e. `[m₀] P₀ = O` or `v_π(x([m₀] P₀)) < 0`. -/
theorem exists_reduction_multiple (N : ℕ) (hN : 1 ≤ N) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ m₀ ≤ N ^ 6 ∧
      ∀ p ∈ N.primeFactors, p ≠ 2 → ∀ π : Zs, ∀ hπ : Prime π, π ∣ (p : Zs) →
        (m₀ : ℤ) • genP0 ∈ E1sub hπ (vge_neg_genD_sq _ hπ) := by
  refine ⟨∏ p ∈ N.primeFactors, orderAbove p, ?_, ?_, ?_⟩
  · exact Finset.one_le_prod fun p _ => orderAbove_pos p
  · calc ∏ p ∈ N.primeFactors, orderAbove p ≤ ∏ p ∈ N.primeFactors, p ^ 6 :=
          Finset.prod_le_prod fun p hp => orderAbove_le (Nat.prime_of_mem_primeFactors hp)
      _ = (∏ p ∈ N.primeFactors, p) ^ 6 := Finset.prod_pow _ _ _
      _ ≤ N ^ 6 := Nat.pow_le_pow_left (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd N)) 6
  · intro p hp hp2 π hπ hπp
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem orderAbove hp
    have := (orderAbove_spec (Nat.prime_of_mem_primeFactors hp) hp2).2.2 π hπ hπp c
    rw [hc]; push_cast; rwa [mul_comm]

end ZInQ.Size
