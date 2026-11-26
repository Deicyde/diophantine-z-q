import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Data.ZMod.Units
import Mathlib.Basic.Real.Basic
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.Conductor

/-! Residue-unit counts for Cox, *Primes of the Form x² + ny²*, §7, Exs. 7.28–7.29. -/

namespace HDec.CMBranch.FowlerArithmetic

open NumberField

local instance (K : Type*) [Field K] [NumberField K] : Infinite (𝓞 K) :=
  Infinite.of_injective (algebraMap ℤ (𝓞 K)) (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))

variable {K : Type*} [Field K] [NumberField K]

/-- For a nonzero prime of the maximal order, the units modulo a positive power are
exactly the classes with nonzero residue modulo the prime. Counting the additive kernel
of reduction gives the norm formula in Cox, Exercise 7.28. -/
theorem card_units_quotient_prime_pow (P : Ideal (𝓞 K)) [P.IsPrime]
    (hP : P ≠ ⊥) (n : ℕ) :
    Nat.card (((𝓞 K) ⧸ P ^ (n + 1))ˣ) = P.absNorm ^ n * (P.absNorm - 1) := by
  classical
  let : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  let : Field ((𝓞 K) ⧸ P) := Ideal.Quotient.field P
  let A := (𝓞 K) ⧸ P ^ (n + 1)
  let B := (𝓞 K) ⧸ P
  let hle : P ^ (n + 1) ≤ P := Ideal.pow_le_self (Nat.succ_ne_zero _)
  let f : A →+* B := Ideal.Quotient.factor hle
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hle
  have hu (a : A) : IsUnit a ↔ f a ≠ 0 := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    change IsUnit (Ideal.Quotient.mk (P ^ (n + 1)) x) ↔
      Ideal.Quotient.mk P x ≠ 0
    rw [Ideal.Quotient.isUnit_mk_pow_iff_notMem P (Nat.succ_ne_zero _)]
    exact not_congr Ideal.Quotient.eq_zero_iff_mem.symm
  let e : Aˣ ≃ {a : A // ¬ f a = 0} :=
    { toFun := fun u => ⟨u, (hu u).mp u.isUnit⟩
      invFun := fun a => ((hu a).mpr a.property).unit
      left_inv := fun u => Units.ext (IsUnit.unit_spec _)
      right_inv := fun a => Subtype.ext (IsUnit.unit_spec ((hu a).mpr a.property)) }
  have hsum := Nat.card_congr (Equiv.sumCompl (fun a : A => f a = 0))
  rw [Nat.card_sum] at hsum
  change Nat.card f.toAddMonoidHom.ker + Nat.card {a : A // ¬ f a = 0} = Nat.card A at hsum
  rw [← Nat.card_congr e] at hsum
  have hB : Nat.card B = P.absNorm := rfl
  have hA : Nat.card A = P.absNorm ^ (n + 1) := by
    change Ideal.absNorm (P ^ (n + 1)) = _
    exact map_pow Ideal.absNorm P (n + 1)
  have hker := AddSubgroup.card_ker_mul_card_of_surjective (f := f.toAddMonoidHom) hf
  rw [hA, hB] at hker
  have hpos : 0 < P.absNorm := Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hP)
  have hker' : Nat.card f.toAddMonoidHom.ker = P.absNorm ^ n :=
    Nat.eq_of_mul_eq_mul_right hpos (hker.trans (pow_succ _ _))
  rw [hker', hA] at hsum
  have hcount : P.absNorm ^ n + P.absNorm ^ n * (P.absNorm - 1) = P.absNorm ^ (n + 1) := by
    calc
      _ = P.absNorm ^ n * (1 + (P.absNorm - 1)) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [Nat.add_sub_of_le hpos, pow_succ]
  change Nat.card Aˣ = _
  omega

open Ideal UniqueFactorizationMonoid

private theorem primeFactors_prod_pow {p : Ideal ℤ} [p.IsMaximal] (hp : p ≠ ⊥) :
    ∏ P : p.primesOver (𝓞 K), P.1 ^ P.1.ramificationIdx ℤ =
      p.map (algebraMap ℤ (𝓞 K)) := by
  classical
  let I := p.map (algebraMap ℤ (𝓞 K))
  have hI : I ≠ ⊥ := map_ne_bot_of_ne_bot hp
  let S := IsDedekindDomain.primesOverFinset p (𝓞 K)
  let e : p.primesOver (𝓞 K) ≃ (S : Set (Ideal (𝓞 K))) :=
    Set.equivOfEq (IsDedekindDomain.coe_primesOverFinset hp (𝓞 K)).symm
  calc
    _ = ∏ P : S, P.1 ^ (factors I).count P.1 := by
      apply Fintype.prod_equiv e
      intro P
      let : P.1.LiesOver p := P.2.2
      change P.1 ^ P.1.ramificationIdx ℤ = P.1 ^ (factors I).count P.1
      rw [IsDedekindDomain.ramificationIdx_eq_factors_count p P.1 hI]
    _ = ∏ P ∈ S, P ^ (factors I).count P :=
      Finset.prod_coe_sort S (fun P => P ^ (factors I).count P)
    _ = ((factors I).map id).prod := (Finset.prod_multiset_map_count (factors I) id).symm
    _ = I := by simpa only [Multiset.map_id] using associated_iff_eq.mp (factors_prod hI)

private theorem rational_span_isMaximal {p : ℕ} (hp : p.Prime) :
    (span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
  (Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr hp.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp) |>.isMaximal (by simpa using hp.ne_zero)

/-- Exact count at the rational prime `p`, using the ramification indices and residue
field degrees of the primes over this very `p`. No discriminant-symbol comparison is needed. -/
theorem card_units_quotient_rational_prime_pow (p : ℕ) (hp : p.Prime) (n : ℕ) :
    let J : Ideal ℤ := span {(p : ℤ)}
    letI : J.IsMaximal := rational_span_isMaximal hp
    Nat.card (((𝓞 K) ⧸ span {((p ^ (n + 1) : ℕ) : 𝓞 K)})ˣ) =
      ∏ P : J.primesOver (𝓞 K),
        (p ^ P.1.inertiaDeg ℤ) ^ (P.1.ramificationIdx ℤ * (n + 1) - 1) *
          (p ^ P.1.inertiaDeg ℤ - 1) := by
  classical
  dsimp only
  let J : Ideal ℤ := span {(p : ℤ)}
  let : J.IsMaximal := rational_span_isMaximal hp
  have hJ : J ≠ ⊥ := by simpa [J] using hp.ne_zero
  have hmap : J.map (algebraMap ℤ (𝓞 K)) = span {(p : 𝓞 K)} := by
    simp [J, Ideal.map_span]
  have hprod : ∏ P : J.primesOver (𝓞 K), P.1 ^ (P.1.ramificationIdx ℤ * (n + 1)) =
      span {((p ^ (n + 1) : ℕ) : 𝓞 K)} := by
    simp only [pow_mul]
    rw [Finset.prod_pow, primeFactors_prod_pow hJ, hmap, Ideal.span_singleton_pow,
      Nat.cast_pow]
  let e := IsDedekindDomain.quotientEquivPiOfProdEq _ Subtype.val
    (fun P : J.primesOver (𝓞 K) => P.1.ramificationIdx ℤ * (n + 1))
    (fun P => Ideal.prime_of_mem_primesOver hJ P.2)
    (fun _ _ h => Subtype.coe_injective.ne h) hprod
  rw [Nat.card_congr ((Units.mapEquiv e.toMulEquiv).trans MulEquiv.piUnits).toEquiv, Nat.card_pi]
  apply Finset.prod_congr rfl
  intro P _
  let : P.1.IsPrime := P.2.1
  let : P.1.LiesOver J := P.2.2
  have hP0 : P.1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hJ P.2
  have he : 0 < P.1.ramificationIdx ℤ :=
    Ideal.ramificationIdx_pos_of_isDedekindDomain' P.1 hJ
  have hr : 0 < P.1.ramificationIdx ℤ * (n + 1) := Nat.mul_pos he (Nat.succ_pos _)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  have hn : P.1.ramificationIdx ℤ * (n + 1) = m + 1 := hm
  rw [hn]
  simpa [← Ideal.pow_inertiaDeg p P.1] using card_units_quotient_prime_pow P.1 hP0 m

/-- The integral Euler cofactor for the splitting of `p` in `K`: `p - 1` for two primes,
`p + 1` for one prime of residue degree two, and `p` otherwise (ramified in degree two). -/
noncomputable def quadraticEulerCofactor (K : Type*) [Field K] [NumberField K] (p : ℕ) : ℕ :=
  let J : Ideal ℤ := span {(p : ℤ)}
  open Classical in
  if Nat.card (J.primesOver (𝓞 K)) = 2 then p - 1
  else if ∃ P : J.primesOver (𝓞 K), P.1.inertiaDeg ℤ = 2 then p + 1 else p

/-- Cox's local conductor factor, before dividing by the scalar units of order
`φ(p ^ (n + 1))`. The cofactor is determined by the actual primes over the same `p`. -/
theorem card_units_quotient_quadratic_prime_pow (hK : Module.finrank ℚ K = 2)
    (p : ℕ) (hp : p.Prime) (n : ℕ) :
    Nat.card (((𝓞 K) ⧸ span {((p ^ (n + 1) : ℕ) : 𝓞 K)})ˣ) =
      (p ^ (n + 1)).totient * (p ^ n * quadraticEulerCofactor K p) := by
  classical
  let J : Ideal ℤ := span {(p : ℤ)}
  let : J.IsMaximal := rational_span_isMaximal hp
  let A := J.primesOver (𝓞 K)
  let e (Q : A) := Q.1.ramificationIdx ℤ
  let d (Q : A) := Q.1.inertiaDeg ℤ
  have hJ : J ≠ ⊥ := by simpa [J] using hp.ne_zero
  have he (Q : A) : 0 < e Q := by
    let : Q.1.IsPrime := Q.2.1
    let : Q.1.LiesOver J := Q.2.2
    exact Ideal.ramificationIdx_pos_of_isDedekindDomain' Q.1 hJ
  have hd (Q : A) : 0 < d Q := by
    let : Q.1.IsPrime := Q.2.1
    exact Ideal.inertiaDeg_pos Q.1 ℤ
  have hsum : ∑ Q : A, e Q * d Q = 2 := by
    rw [Ideal.sum_ramification_inertia_eq_finrank J (𝓞 K), RingOfIntegers.rank, hK]
  have hle : Fintype.card A ≤ 2 := by
    calc
      Fintype.card A = ∑ _ : A, 1 := by simp
      _ ≤ ∑ Q : A, e Q * d Q :=
        Finset.sum_le_sum fun Q _ => Nat.mul_pos (he Q) (hd Q)
      _ = 2 := hsum
  have hne : Fintype.card A ≠ 0 := by
    obtain ⟨Q, hQ, hQJ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) J
    let : Nonempty A := ⟨⟨Q, hQ.isPrime, hQJ⟩⟩
    exact Fintype.card_ne_zero
  have hprod := card_units_quotient_rational_prime_pow (K := K) p hp n
  change _ = ∏ Q : A, (p ^ d Q) ^ (e Q * (n + 1) - 1) * (p ^ d Q - 1) at hprod
  rw [hprod, Nat.totient_prime_pow_succ hp]
  unfold quadraticEulerCofactor
  dsimp only
  rw [Nat.card_eq_fintype_card]
  rcases (show Fintype.card A = 1 ∨ Fintype.card A = 2 by omega) with hcard | hcard
  · let f := (Fintype.equivFinOfCardEq hcard).symm
    rw [← f.sum_comp, Fin.sum_univ_one] at hsum
    rw [← f.prod_comp, Fin.prod_univ_one, hcard, ite_eq_right (by decide : ¬ 1 = 2)]
    have hle' : e (f 0) ≤ 2 ∧ d (f 0) ≤ 2 := by
      constructor
      · exact hsum ▸ Nat.le_mul_of_pos_right _ (hd (f 0))
      · exact hsum ▸ Nat.le_mul_of_pos_left _ (he (f 0))
    have hcases : (e (f 0) = 1 ∧ d (f 0) = 2) ∨ (e (f 0) = 2 ∧ d (f 0) = 1) := by
      by_cases h : e (f 0) = 1
      · left; simpa [h] using hsum
      · have he' : e (f 0) = 2 := by have := he (f 0); omega
        right
        simp only [he', true_and]
        rw [he', Nat.two_mul] at hsum
        omega
    rcases hcases with ⟨he', hd'⟩ | ⟨he', hd'⟩
    · rw [ite_eq_left ⟨f 0, hd'⟩, he', hd', one_mul, Nat.add_sub_cancel]
      have hs : p ^ 2 - 1 = (p - 1) * (p + 1) := by
        rw [Nat.sub_mul, one_mul, pow_two, Nat.mul_add, Nat.mul_one]
        omega
      rw [hs, ← pow_mul, two_mul, pow_add]
      ac_rfl
    · have hx : ¬ ∃ Q : A, d Q = 2 := by
        rintro ⟨Q, hQ⟩
        obtain ⟨i, rfl⟩ := f.surjective Q
        have : i = 0 := Subsingleton.elim _ _
        rw [this, hd'] at hQ
        omega
      rw [ite_eq_right hx, he', hd', pow_one]
      have hh : 2 * (n + 1) - 1 = n + n + 1 := by omega
      rw [hh, pow_succ, pow_add]
      ac_rfl
  · let f := (Fintype.equivFinOfCardEq hcard).symm
    rw [← f.sum_comp, Fin.sum_univ_two] at hsum
    have hdeg (i : Fin 2) (hi : e (f i) * d (f i) = 1) : e (f i) = 1 ∧ d (f i) = 1 := by
      simpa using hi
    have hp0 := Nat.mul_pos (he (f 0)) (hd (f 0))
    have hp1 := Nat.mul_pos (he (f 1)) (hd (f 1))
    have h0 := hdeg 0 (by omega)
    have h1 := hdeg 1 (by omega)
    rw [← f.prod_comp, Fin.prod_univ_two, hcard, ite_eq_left rfl]
    simp only [h0.1, h0.2, h1.1, h1.2, pow_one, one_mul, Nat.add_sub_cancel]

omit [NumberField K] in
private theorem card_units_quotient_span_mul (a b : ℕ) (hab : a.Coprime b) :
    Nat.card (((𝓞 K) ⧸ span {((a * b : ℕ) : 𝓞 K)})ˣ) =
      Nat.card (((𝓞 K) ⧸ span {(a : 𝓞 K)})ˣ) *
        Nat.card (((𝓞 K) ⧸ span {(b : 𝓞 K)})ˣ) := by
  have hc : IsCoprime (span {(a : 𝓞 K)}) (span {(b : 𝓞 K)}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr (by
      simpa using hab.isCoprime.map (algebraMap ℤ (𝓞 K)))
  let e := Ideal.quotientMulEquivQuotientProd _ _ hc
  rw [Nat.cast_mul, ← span_singleton_mul_span_singleton]
  rw [Nat.card_congr ((Units.mapEquiv e.toMulEquiv).trans MulEquiv.prodUnits).toEquiv,
    Nat.card_prod]

/-- Multiplying the local Euler factors over the rational prime divisors of `f` gives
Cox's count in the actual residue ring `𝓞 K / f 𝓞 K`, including `f = 1`. -/
theorem card_units_quotient_quadratic_conductor (hK : Module.finrank ℚ K = 2)
    (f : ℕ) (hf : f ≠ 0) :
    Nat.card (((𝓞 K) ⧸ span {(f : 𝓞 K)})ˣ) = f.totient *
      ∏ p ∈ f.primeFactors, p ^ (f.factorization p - 1) * quadraticEulerCofactor K p := by
  classical
  let u (m : ℕ) := Nat.card (((𝓞 K) ⧸ span {(m : 𝓞 K)})ˣ)
  have h1 : u 1 = 1 := by
    let : Subsingleton ((𝓞 K) ⧸ span {((1 : ℕ) : 𝓞 K)}) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    exact Nat.card_unique
  change u f = _
  rw [Nat.multiplicative_factorization u (card_units_quotient_span_mul (K := K)) h1 hf,
    Nat.prod_factorization_eq_prod_primeFactors]
  calc
    _ = ∏ p ∈ f.primeFactors, (p ^ f.factorization p).totient *
          (p ^ (f.factorization p - 1) * quadraticEulerCofactor K p) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hpos : 0 < f.factorization p := by
        rw [← Nat.support_factorization] at hp
        exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      have heq : f.factorization p = n + 1 := hn
      rw [heq]
      simpa [u] using card_units_quotient_quadratic_prime_pow hK p
        (Nat.prime_of_mem_primeFactors hp) n
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      congr 1
      exact (Nat.prod_factorization_eq_prod_primeFactors _).symm.trans
        (Nat.multiplicative_factorization Nat.totient (@Nat.totient_mul) Nat.totient_one hf).symm

/-- The splitting sign of a rational prime: `1` for split, `-1` for inert and `0` for ramified
in a quadratic field. This is defined from the primes of the maximal order, not the discriminant. -/
noncomputable def quadraticSplittingSymbol (K : Type*) [Field K] [NumberField K] (p : ℕ) : ℤ :=
  let J : Ideal ℤ := span {(p : ℤ)}
  open Classical in
  if Nat.card (J.primesOver (𝓞 K)) = 2 then 1
  else if ∃ P : J.primesOver (𝓞 K), P.1.inertiaDeg ℤ = 2 then -1 else 0

theorem quadraticSplittingSymbol_le_one (p : ℕ) : quadraticSplittingSymbol K p ≤ 1 := by
  unfold quadraticSplittingSymbol
  dsimp only
  split_ifs <;> decide

/-- The cofactor has the division-free form `p - χ_K(p)` over the integers. -/
theorem intCast_quadraticEulerCofactor (p : ℕ) (hp : p.Prime) :
    (quadraticEulerCofactor K p : ℤ) = (p : ℤ) - quadraticSplittingSymbol K p := by
  unfold quadraticEulerCofactor quadraticSplittingSymbol
  dsimp only
  split_ifs
  · exact Int.ofNat_sub (Nat.one_le_of_lt hp.one_lt)
  · simp
  · simp

/-- The same count on the conductor ideal of the given order. No Picard group is used. -/
theorem card_units_quotient_order_conductor (O : TauCeti.GlobalNumberFields.NumberFieldOrder K)
    (hK : Module.finrank ℚ K = 2) :
    Nat.card (((𝓞 K) ⧸ O.conductor)ˣ) = O.index.totient *
      ∏ p ∈ O.index.primeFactors,
        p ^ (O.index.factorization p - 1) * quadraticEulerCofactor K p := by
  rw [O.conductor_eq_span_index hK]
  exact card_units_quotient_quadratic_conductor hK O.index O.index_ne_zero

/-- Cox's Euler product on the conductor of this order. The symbol is the splitting sign
of the same rational prime in `K`; no class number or order-unit index enters this calculation. -/
theorem card_units_quotient_order_conductor_real
    (O : TauCeti.GlobalNumberFields.NumberFieldOrder K) (hK : Module.finrank ℚ K = 2) :
    (Nat.card (((𝓞 K) ⧸ O.conductor)ˣ) : ℝ) = (O.index.totient : ℝ) *
      ((O.index : ℝ) * ∏ p ∈ O.index.primeFactors,
        (1 - (quadraticSplittingSymbol K p : ℝ) / (p : ℝ))) := by
  rw [card_units_quotient_order_conductor O hK, Nat.cast_mul, Nat.cast_prod]
  congr 1
  conv_rhs => lhs; rw [Nat.prod_primeFactors_pow_factorization O.index_ne_zero, Nat.cast_prod]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hk : 0 < O.index.factorization p := by
    rw [← Nat.support_factorization] at hp
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hprime.ne_zero
  have hc := congrArg (fun z : ℤ => (z : ℝ))
    (intCast_quadraticEulerCofactor (K := K) p hprime)
  push_cast at hc ⊢
  have heq : (p : ℝ) ^ O.index.factorization p =
      (p : ℝ) ^ (O.index.factorization p - 1) * (p : ℝ) := by
    conv_lhs => rw [← Nat.sub_add_cancel hk, pow_succ]
  rw [hc, heq]
  field_simp

end HDec.CMBranch.FowlerArithmetic
