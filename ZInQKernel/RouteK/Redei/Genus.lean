import ZInQKernel.RouteK.Redei.Entry

/-!
# Rédei's formula, step 4: genus characters (`docs/research/redei-plan.md` §3.2)

`K = QNeg n`, `O = 𝓞 K`, `n` odd squarefree, `q` a prime of `n`, `𝔭_q` the prime of `O` above `q`.

* `exists_mk0_coprime`: every ideal class contains an integral ideal of norm prime to `q`
  (`IsDedekindDomain.exists_sup_span_eq` applied to `J (q) ≤ J` for `J` in the inverse class);
* `isSquare_normZ_mod`: for every `x : O`, `N(x)` is a square mod `q`. Indeed `σ` acts trivially on
  `O/𝔭_q = 𝔽_q` (`sub_conj_mem`), so `N(x) = x σ(x) ≡ x² ≡ m² (mod 𝔭_q)` for an integer `m`;
* `legBit_absNorm_eq_of_mk0_eq`: the bit `[N𝔞/q]` depends only on the class of `𝔞` (for `𝔞` prime
  to `q`). If `𝔞`, `𝔟` are in the same class, take `𝔠` prime to `q` in the inverse class; then
  `𝔞𝔠 = (α)` and `𝔟𝔠 = (β)`, and `N𝔞 N𝔠 = N(α)`, `N𝔟 N𝔠 = N(β)` are squares mod `q`;
* `chi n q : ClassGroup O →* Multiplicative (ZMod 2)`, the genus character `χ_q([𝔞]) = [N𝔞/q]`,
  defined through a chosen representative prime to `q`; `chi_mk0`;
* `chi_ramIdeal`: `χ_q([𝔭_p]) = R_{qp}` (`redeiEntry`), for every `p ∈ ramSet n`. For `p = q` this
  uses `𝔭_q · Π_{p ≠ q} 𝔭_p = (√−n)` (`span_omega`);
* `chi_prod_ramIdeal`: `χ_q(Π_p [𝔭_p]^{e_p}) = Σ_p R_{qp} e_p`, the plan's `chi_psi` without `psi`.
-/

noncomputable section

open NumberField Pointwise
open scoped nonZeroDivisors

namespace ZInQ.RouteK.Redei

open ZInQ.RouteK.Rank5b

section Genus

variable (n : ℕ) [NeZero n]

local notation "K" => QNeg n
local notation "O" => 𝓞 (QNeg n)

variable {n}

/-! ### Representatives prime to `q` -/

/-- If `I + (q) = O`, then `q ∤ N I`. -/
theorem not_dvd_absNorm_of_sup_span_eq_top {q : ℕ} (hq : q.Prime) {I : Ideal O}
    (h : I ⊔ Ideal.span {(q : O)} = ⊤) : ¬ q ∣ Ideal.absNorm I := by
  intro hd
  obtain ⟨P, hPm, hPu, hPI⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hq I hd
  have hqP : (q : O) ∈ P := by
    have : (q : ℤ) ∈ P.under ℤ := by rw [hPu]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.under_def, Ideal.mem_comap] at this
    simpa using this
  have hle : I ⊔ Ideal.span {(q : O)} ≤ P :=
    sup_le (Ideal.le_of_dvd hPI) ((Ideal.span_singleton_le_iff_mem _).2 hqP)
  rw [h] at hle
  exact hPm.ne_top (top_le_iff.1 hle)

variable (n) in
/-- Every class contains an integral ideal prime to `q`. -/
theorem exists_mk0_coprime (q : ℕ) (hq : q.Prime) (c : ClassGroup O) :
    ∃ I : (Ideal O)⁰, ClassGroup.mk0 I = c ∧ ¬ q ∣ Ideal.absNorm (I : Ideal O) := by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective c⁻¹
  have hJ0 : (J : Ideal O) ≠ 0 := nonZeroDivisors.coe_ne_zero J
  have hq0 : Ideal.span {(q : O)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact natCast_ne_zero_O hq.ne_zero
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
    (I := (J : Ideal O) * Ideal.span {(q : O)}) (J := J) (Ideal.mul_le_inf.trans inf_le_left) (mul_ne_zero hJ0 hq0)
  have haJ : a ∈ (J : Ideal O) := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨M, hM⟩ := Ideal.dvd_span_singleton.2 haJ
  have hcop : M ⊔ Ideal.span {(q : O)} = ⊤ := by
    have h1 : (J : Ideal O) * (Ideal.span {(q : O)} ⊔ M) = J * ⊤ := by
      rw [Ideal.mul_sup, ← hM, ha, Ideal.mul_top]
    rw [sup_comm]; exact mul_left_cancel₀ hJ0 h1
  have hM0 : M ≠ 0 := by
    rintro rfl
    rw [Ideal.zero_eq_bot, bot_sup_eq, Ideal.span_singleton_eq_top, isUnit_iff_dvd_one,
      show (1 : O) = ((1 : ℕ) : O) by simp, natCast_dvd_natCast_iff] at hcop
    exact hq.one_lt.ne' (Nat.dvd_one.1 hcop)
  set M' : (Ideal O)⁰ := ⟨M, mem_nonZeroDivisors_of_ne_zero hM0⟩
  refine ⟨M', ?_, not_dvd_absNorm_of_sup_span_eq_top hq hcop⟩
  have h1 : ClassGroup.mk0 J * ClassGroup.mk0 M' = 1 := by
    rw [← map_mul, ClassGroup.mk0_eq_one_iff (J * M').2]
    have e : ((J * M' : (Ideal O)⁰) : Ideal O) = Ideal.span {a} := by
      rw [Submonoid.coe_mul]; exact hM.symm
    rw [e]
    exact ⟨⟨a, rfl⟩⟩
  rw [hJ] at h1
  exact (inv_mul_eq_one.1 h1).symm

/-! ### Norms are squares mod `q` -/

/-- For `q ∣ n` (`n` squarefree) and `x : O`, `N(x)` is a square mod `q`: `σ` acts trivially on
`O/𝔭_q`, so `N(x) = x σ(x) ≡ x² ≡ m² (mod 𝔭_q)`. -/
theorem isSquare_normZ_mod (hsq : Squarefree n) {q : ℕ} (hq : q ∈ n.primeFactors) (x : O) :
    IsSquare ((Algebra.norm ℤ x : ℤ) : ZMod q) := by
  obtain ⟨σ, hσ⟩ := exists_conj_ne_one (n := n)
  have hqp := Nat.prime_of_mem_primeFactors hq
  have := ramIdeal_isMaximal (n := n) hqp
  have := ramIdeal_liesOver (n := n) hqp
  have hsq2 : ramIdeal n q ^ 2 = Ideal.span {(q : O)} :=
    ramified_of_dvd hsq hqp (Nat.dvd_of_mem_primeFactors hq) _
  have hN : Ideal.absNorm (ramIdeal n q) = q := absNorm_of_ramified _ hsq2
  have hs : σ • ramIdeal n q = ramIdeal n q :=
    smul_eq_of_pow_le σ _ (k := 2) (by rw [hsq2]; exact span_le_smul_of_liesOver σ _)
  obtain ⟨m, hm⟩ := exists_int_sub_mem_of_absNorm (ramIdeal n q) hqp hN x
  have h1 := sub_conj_mem σ (ramIdeal n q) hs hqp hN x
  have key : ((Algebra.norm ℤ x - m ^ 2 : ℤ) : O) ∈ ramIdeal n q := by
    have e : ((Algebra.norm ℤ x - m ^ 2 : ℤ) : O) = x * (-(x - σ • x)) + (x - m) * (x + m) := by
      rw [Int.cast_sub, normZ_eq_mul_conj σ hσ x]; push_cast; ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.neg_mem_iff _ |>.2 h1))
      (Ideal.mul_mem_right _ _ hm)
  rw [intCast_mem_iff_of_liesOver (p := q) (ramIdeal n q)] at key
  refine ⟨(m : ZMod q), ?_⟩
  have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).2 key
  push_cast at h2
  linear_combination h2

/-- `[N(x)/q] = 0` for a principal ideal `(x)`. -/
theorem legBit_absNorm_span (hsq : Squarefree n) {q : ℕ} (hq : q ∈ n.primeFactors) (x : O) :
    legBit q ((Ideal.absNorm (Ideal.span {x}) : ℕ) : ℤ) = 0 := by
  rw [Ideal.absNorm_span_singleton, Int.natCast_natAbs, abs_of_nonneg (normZ_nonneg x)]
  unfold legBit
  rw [ite_eq_left (isSquare_normZ_mod hsq hq x)]

theorem intCast_natCast_zmod_ne_zero {q m : ℕ} (h : ¬ q ∣ m) : (((m : ℤ)) : ZMod q) ≠ 0 := by
  rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]; exact h

/-- `[N(IJ)/q] = [N I/q] + [N J/q]` for `I`, `J` prime to `q`. -/
theorem legBit_absNorm_mul {q : ℕ} (hq : q.Prime) {I J : Ideal O}
    (hI : ¬ q ∣ Ideal.absNorm I) (hJ : ¬ q ∣ Ideal.absNorm J) :
    legBit q ((Ideal.absNorm (I * J) : ℕ) : ℤ) =
      legBit q ((Ideal.absNorm I : ℕ) : ℤ) + legBit q ((Ideal.absNorm J : ℕ) : ℤ) := by
  have := Fact.mk hq
  rw [map_mul, Nat.cast_mul]
  exact legBit_mul (intCast_natCast_zmod_ne_zero hI) (intCast_natCast_zmod_ne_zero hJ)

theorem not_dvd_absNorm_mul {q : ℕ} (hq : q.Prime) {I J : Ideal O}
    (hI : ¬ q ∣ Ideal.absNorm I) (hJ : ¬ q ∣ Ideal.absNorm J) : ¬ q ∣ Ideal.absNorm (I * J) := by
  rw [map_mul]; exact fun h => (hq.dvd_mul.1 h).elim hI hJ

/-- **Well-definedness of `χ_q`**: `[N𝔞/q]` depends only on the class of `𝔞` prime to `q`. -/
theorem legBit_absNorm_eq_of_mk0_eq (hsq : Squarefree n) {q : ℕ} (hq : q ∈ n.primeFactors)
    {I J : (Ideal O)⁰} (hIJ : ClassGroup.mk0 I = ClassGroup.mk0 J)
    (hI : ¬ q ∣ Ideal.absNorm (I : Ideal O)) (hJ : ¬ q ∣ Ideal.absNorm (J : Ideal O)) :
    legBit q ((Ideal.absNorm (I : Ideal O) : ℕ) : ℤ) =
      legBit q ((Ideal.absNorm (J : Ideal O) : ℕ) : ℤ) := by
  have hqp := Nat.prime_of_mem_primeFactors hq
  obtain ⟨M, hM, hMq⟩ := exists_mk0_coprime n q hqp (ClassGroup.mk0 I)⁻¹
  have key : ∀ L : (Ideal O)⁰, ClassGroup.mk0 L = ClassGroup.mk0 I →
      ¬ q ∣ Ideal.absNorm (L : Ideal O) →
      legBit q ((Ideal.absNorm (L : Ideal O) : ℕ) : ℤ) =
        legBit q ((Ideal.absNorm (M : Ideal O) : ℕ) : ℤ) := by
    intro L hL hLq
    have h1 : ClassGroup.mk0 (L * M) = 1 := by rw [map_mul, hL, hM, mul_inv_cancel]
    obtain ⟨⟨x, hx⟩⟩ := (ClassGroup.mk0_eq_one_iff (L * M).2).1 h1
    have h2 := legBit_absNorm_span hsq hq x
    have hx' : ((L * M : (Ideal O)⁰) : Ideal O) = Ideal.span {x} := hx
    rw [← hx', Submonoid.coe_mul, legBit_absNorm_mul hqp hLq hMq] at h2
    have h3 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact h3 _ _ h2
  rw [key I rfl hI, key J hIJ.symm hJ]

/-! ### The genus character -/

variable (n) in
/-- The bit of `χ_q` on a class: `[N𝔞/q]` for a chosen representative `𝔞` prime to `q`. -/
def chiBit (q : n.primeFactors) (c : ClassGroup O) : ZMod 2 :=
  legBit q ((Ideal.absNorm ((Classical.choose
    (exists_mk0_coprime n q (Nat.prime_of_mem_primeFactors q.2) c) : (Ideal O)⁰) : Ideal O) : ℕ) :
      ℤ)

theorem chiBit_mk0 (hsq : Squarefree n) (q : n.primeFactors) (I : (Ideal O)⁰)
    (hI : ¬ (q : ℕ) ∣ Ideal.absNorm (I : Ideal O)) :
    chiBit n q (ClassGroup.mk0 I) = legBit q ((Ideal.absNorm (I : Ideal O) : ℕ) : ℤ) := by
  have h := Classical.choose_spec
    (exists_mk0_coprime n q (Nat.prime_of_mem_primeFactors q.2) (ClassGroup.mk0 I))
  exact legBit_absNorm_eq_of_mk0_eq hsq q.2 h.1 h.2 hI

theorem chiBit_mul (hsq : Squarefree n) (q : n.primeFactors) (c d : ClassGroup O) :
    chiBit n q (c * d) = chiBit n q c + chiBit n q d := by
  have hqp := Nat.prime_of_mem_primeFactors q.2
  obtain ⟨I, rfl, hI⟩ := exists_mk0_coprime n q hqp c
  obtain ⟨J, rfl, hJ⟩ := exists_mk0_coprime n q hqp d
  have hIJ : ¬ (q : ℕ) ∣ Ideal.absNorm ((I * J : (Ideal O)⁰) : Ideal O) := by
    rw [Submonoid.coe_mul]; exact not_dvd_absNorm_mul hqp hI hJ
  rw [← map_mul, chiBit_mk0 hsq q _ hIJ, chiBit_mk0 hsq q _ hI, chiBit_mk0 hsq q _ hJ,
    Submonoid.coe_mul, legBit_absNorm_mul hqp hI hJ]

variable (n) in
/-- The genus character `χ_q([𝔞]) = (N𝔞 / q)`, for a prime `q ∣ n` (`n` squarefree; `1` if `n`
is not squarefree). -/
def chi (q : n.primeFactors) : ClassGroup O →* Multiplicative (ZMod 2) :=
  if hsq : Squarefree n then
    MonoidHom.mk' (fun c => Multiplicative.ofAdd (chiBit n q c)) fun c d => by
      rw [chiBit_mul hsq, ofAdd_add]
  else 1

variable (n) in
theorem chi_mk0 (_hn : Odd n) (hsq : Squarefree n) (q : n.primeFactors) (I : (Ideal O)⁰)
    (hI : ¬ (q : ℕ) ∣ Ideal.absNorm (I : Ideal O)) :
    chi n q (ClassGroup.mk0 I) =
      Multiplicative.ofAdd (legBit q ((Ideal.absNorm (I : Ideal O) : ℕ) : ℤ)) := by
  rw [chi, dite_eq_left hsq, MonoidHom.mk'_apply, chiBit_mk0 hsq q I hI]

/-! ### The genus characters on the ramified primes -/

/-- `χ_q([𝔭_q]) = [(n/q)/q]`: `𝔭_q Π_{p ≠ q} 𝔭_p = (√−n)` is principal, and
`N(Π_{p ≠ q} 𝔭_p) = n/q`. -/
theorem chi_ramIdeal_self (hn : Odd n) (hsq : Squarefree n) (q : n.primeFactors) :
    chi n q (ClassGroup.mk0 ⟨ramIdeal n q, ramIdeal_mem n q⟩) =
      Multiplicative.ofAdd (legBit q ((n / q : ℕ) : ℤ)) := by
  have hqp := Nat.prime_of_mem_primeFactors q.2
  set s := n.primeFactors.erase (q : ℕ)
  set J : Ideal O := ∏ p ∈ s, ramIdeal n p
  have hJ0 : J ∈ (Ideal O)⁰ :=
    mem_nonZeroDivisors_of_ne_zero (Finset.prod_ne_zero_iff.2 fun p _ => ramIdeal_ne_bot)
  have hNJ : Ideal.absNorm J = ∏ p ∈ s, p := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    exact (ramIdeal_spec n hn hsq
      (mem_ramSet_of_mem_primeFactors (Finset.mem_of_mem_erase hp))).2.2
  have hdiv : n / q = ∏ p ∈ s, p := by
    refine Nat.div_eq_of_eq_mul_right hqp.pos ?_
    rw [Finset.mul_prod_erase _ (fun p => p) q.2, Nat.prod_primeFactors_of_squarefree hsq]
  have hJq : ¬ (q : ℕ) ∣ Ideal.absNorm J := by
    rw [hNJ, Prime.dvd_finsetProd_iff hqp.prime]
    rintro ⟨p, hp, hqp'⟩
    exact (Finset.ne_of_mem_erase hp)
      ((Nat.prime_dvd_prime_iff_eq hqp
        (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp))).1 hqp').symm
  have hprod : ClassGroup.mk0 (⟨ramIdeal n q, ramIdeal_mem n q⟩ : (Ideal O)⁰) *
      ClassGroup.mk0 (⟨J, hJ0⟩ : (Ideal O)⁰) = 1 := by
    rw [← map_mul]
    have h1 : ramIdeal n q * J = Ideal.span {omegaO n} := by
      rw [Finset.mul_prod_erase _ (fun p => ramIdeal n p) q.2]
      exact (span_omega n hn hsq).symm
    have h2 : (⟨ramIdeal n q, ramIdeal_mem n q⟩ : (Ideal O)⁰) * ⟨J, hJ0⟩ =
        ⟨Ideal.span {omegaO n}, by rw [← h1]; exact Submonoid.mul_mem _ (ramIdeal_mem n q) hJ0⟩ :=
      Subtype.ext h1
    rw [h2, ClassGroup.mk0_eq_one_iff]
    exact ⟨⟨omegaO n, rfl⟩⟩
  have h3 := congrArg (chi n q) hprod
  rw [map_mul, map_one, chi_mk0 n hn hsq q ⟨J, hJ0⟩ hJq, ← eq_inv_iff_mul_eq_one] at h3
  rw [h3, ← ofAdd_neg, ZMod.neg_eq_self_mod_two]
  change Multiplicative.ofAdd (legBit q ((Ideal.absNorm J : ℕ) : ℤ)) = _
  rw [hNJ, hdiv]

variable (n) in
/-- **The genus characters on the ramified primes**: `χ_q([𝔭_p]) = R_{qp}`, the entry of the
Rédei matrix. -/
theorem chi_ramIdeal (hn : Odd n) (hsq : Squarefree n) (q : n.primeFactors) (p : ramSet n) :
    chi n q (ClassGroup.mk0 ⟨ramIdeal n p, ramIdeal_mem n p⟩) =
      Multiplicative.ofAdd (redeiEntry n q p) := by
  have hqp := Nat.prime_of_mem_primeFactors q.2
  have hq2 : (q : ℕ) ≠ 2 := by
    rintro h
    have := Nat.dvd_of_mem_primeFactors q.2
    rw [h] at this
    exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 this)
  have hpp := prime_of_mem_ramSet p.2
  have hNp := (ramIdeal_spec n hn hsq p.2).2.2
  unfold redeiEntry
  split_ifs with h2 hpq
  · have hI : ¬ (q : ℕ) ∣ Ideal.absNorm (ramIdeal n p) := by
      rw [hNp, h2]
      exact fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).1 h)
    rw [chi_mk0 n hn hsq q ⟨ramIdeal n p, ramIdeal_mem n p⟩ hI]
    change Multiplicative.ofAdd (legBit q ((Ideal.absNorm (ramIdeal n p) : ℕ) : ℤ)) = _
    rw [hNp, h2]; rfl
  · have e : (⟨ramIdeal n p, ramIdeal_mem n p⟩ : (Ideal O)⁰) =
        ⟨ramIdeal n q, ramIdeal_mem n q⟩ := Subtype.ext (by rw [hpq])
    rw [e]
    exact chi_ramIdeal_self hn hsq q
  · have hI : ¬ (q : ℕ) ∣ Ideal.absNorm (ramIdeal n p) := by
      rw [hNp]
      exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq hqp hpp).1 h).symm
    rw [chi_mk0 n hn hsq q ⟨ramIdeal n p, ramIdeal_mem n p⟩ hI]
    change Multiplicative.ofAdd (legBit q ((Ideal.absNorm (ramIdeal n p) : ℕ) : ℤ)) = _
    rw [hNp]

variable (n) in
/-- `χ_q(Π_p [𝔭_p]^{e_p}) = Σ_p R_{qp} e_p`. With `ψ(e) = Π_p [𝔭_p]^{e_p}` (step 3, `psi`), this is
the plan's `chi_psi`. -/
theorem chi_prod_ramIdeal (hn : Odd n) (hsq : Squarefree n) (q : n.primeFactors)
    (e : ramSet n → ZMod 2) :
    Multiplicative.toAdd (chi n q (∏ p : ramSet n,
      ClassGroup.mk0 (⟨ramIdeal n p, ramIdeal_mem n p⟩ : (Ideal O)⁰) ^ (e p).val)) =
      ∑ p, redeiEntry n q p * e p := by
  rw [map_prod, toAdd_prod]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_pow, chi_ramIdeal n hn hsq q p, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul,
    ZMod.natCast_zmod_val, mul_comm]

end Genus

end ZInQ.RouteK.Redei
