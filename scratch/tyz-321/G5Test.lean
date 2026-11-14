import ZInQKernel.Contrib.TYZGenus.RingClassBridge
import ZInQKernel.Contrib.TYZGenus.ShimuraFricke

noncomputable section

namespace ZInQ.Contrib.TYZGenus.T321G

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Package
  ZInQ.Contrib.TYZGenus.RingClass ZInQ.PropN NumberField
  TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZGenus.RingClassBridge ZInQ.RouteK.Redei
open scoped nonZeroDivisors

def varpiIdeal (d : ℕ) [NeZero d] : Ideal (𝓞 (QNeg d)) :=
  Ideal.span {(((d + 1) / 2 : ℕ) : 𝓞 (QNeg d)), sqrtNeg d - 1}

open Classical in
def wClass (d : ℕ) [NeZero d] : Pic (O4 d) :=
  if h : varpiIdeal d ∈ integralIdealsPrimeTo (O4 d).conductorModulus then (O4 d).picClass ⟨_, h⟩
  else 1


variable {n : ℕ} [NeZero n]
def hW0 (n : ℕ) : QNeg n := ⟨((n : ℚ) + 1) / 2, 0⟩
def hW1 (n : ℕ) : QNeg n := ⟨-4, 4⟩

@[simp] theorem hW0_re : (hW0 n).re = ((n : ℚ) + 1) / 2 := rfl
@[simp] theorem hW0_im : (hW0 n).im = 0 := rfl
@[simp] theorem hW1_re : (hW1 n).re = -4 := rfl
@[simp] theorem hW1_im : (hW1 n).im = 4 := rfl

theorem natCast_m (hn : n % 8 = 5) : (((n + 1) / 2 : ℕ) : ℚ) = ((n : ℚ) + 1) / 2 := by
  have : (n + 1) / 2 * 2 = n + 1 := by omega
  have h' : (((n + 1) / 2 : ℕ) : ℚ) * 2 = (n : ℚ) + 1 := by exact_mod_cast this
  linarith

theorem coe_m (hn : n % 8 = 5) :
    (((((n + 1) / 2 : ℕ) : 𝓞 (QNeg n))) : QNeg n) = hW0 n := by
  have h2 : (((n + 1) / 2 : ℕ) : ℚ) = ((n : ℚ) + 1) / 2 := by
    have : (n + 1) / 2 * 2 = n + 1 := by omega
    have h' : (((n + 1) / 2 : ℕ) : ℚ) * 2 = (n : ℚ) + 1 := by exact_mod_cast this
    linarith
  rw [show ((((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) : QNeg n) = (((n + 1) / 2 : ℕ) : QNeg n) from
    map_natCast (algebraMap (𝓞 (QNeg n)) (QNeg n)) _]
  ext
  · rw [QuadraticAlgebra.re_natCast, h2]; rfl
  · rw [QuadraticAlgebra.im_natCast]; rfl

theorem varpiIdeal_mem (hn : n % 8 = 5) :
    varpiIdeal n ∈ integralIdealsPrimeTo (O4 n).conductorModulus := by
  rw [Modulus.mem_integralIdealsPrimeTo, Modulus.isCoprimeTo_iff_sup_eq_top,
    conductorModulus_finitePart]
  have key : (1 : 𝓞 (QNeg n)) = (-1) * (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) +
      4 * (((n + 3) / 8 : ℕ) : 𝓞 (QNeg n)) := by
    have h' : (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) + 1 = 4 * (((n + 3) / 8 : ℕ) : 𝓞 (QNeg n)) := by
      exact_mod_cast (show (n + 1) / 2 + 1 = 4 * ((n + 3) / 8) by omega)
    linear_combination h'
  refine ⟨?_, ?_⟩
  · intro h
    have hmem : (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) ∈ varpiIdeal n :=
      Ideal.subset_span (Set.mem_insert _ _)
    rw [h, Ideal.mem_bot] at hmem
    have h2 := congrArg (fun x : 𝓞 (QNeg n) => ((x : QNeg n)).re) hmem
    simp only [coe_m hn, hW0] at h2
    simp at h2
    have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    linarith
  · rw [Ideal.eq_top_iff_one, key]
    refine Ideal.add_mem _ (Ideal.mem_sup_left
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))) (Ideal.mem_sup_right ?_)
    simpa using natCast_mul_mem_conductor (QNeg n) 4 ((((n + 3) / 8 : ℕ)) : 𝓞 (QNeg n))

theorem wClass_eq (hn : n % 8 = 5) : wClass n = (O4 n).picClass ⟨_, varpiIdeal_mem hn⟩ := by
  unfold wClass; rw [dif_pos (varpiIdeal_mem hn)]


/-- The ramified prime `𝔭₂ = (2, √−n − 1)` of `𝓞_{K_n}` (`n ≡ 1 (mod 4)`). -/
def p2Ideal5 (n : ℕ) [NeZero n] : Ideal (𝓞 (QNeg n)) := Ideal.span {2, sqrtNeg n - 1}

theorem varpi_sq_add (n : ℕ) [NeZero n] :
    (sqrtNeg n - 1) * (sqrtNeg n - 1) + 2 * (sqrtNeg n - 1) = -((n : 𝓞 (QNeg n)) + 1) := by
  linear_combination sqrtNeg_mul_self (d := n)

theorem p2_sq (hn : n % 8 = 5) : p2Ideal5 n * p2Ideal5 n = Ideal.span {2} := by
  rw [p2Ideal5, Ideal.span_pair_mul_span_pair]
  have hv := varpi_sq_add n
  have hk : (n : 𝓞 (QNeg n)) + 1 = 8 * ((n / 8 : ℕ) : 𝓞 (QNeg n)) + 6 := by
    have : n + 1 = 8 * (n / 8) + 6 := by omega
    exact_mod_cast this
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨2, by ring⟩
    · exact ⟨sqrtNeg n - 1, rfl⟩
    · exact ⟨sqrtNeg n - 1, by ring⟩
    · exact ⟨-(4 * ((n / 8 : ℕ) : 𝓞 (QNeg n)) + 3) - (sqrtNeg n - 1), by linear_combination hv - hk⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    set S : Set (𝓞 (QNeg n)) := {2 * 2, 2 * (sqrtNeg n - 1), (sqrtNeg n - 1) * 2,
      (sqrtNeg n - 1) * (sqrtNeg n - 1)} with hS
    have e : (2 : 𝓞 (QNeg n)) = (-1) * ((sqrtNeg n - 1) * (sqrtNeg n - 1)) +
        (-1) * (2 * (sqrtNeg n - 1)) + (-(2 * ((n / 8 : ℕ) : 𝓞 (QNeg n)) + 1)) * (2 * 2) := by
      linear_combination hv - hk
    rw [e]
    refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_))
      (Ideal.mul_mem_left _ _ ?_)
    · exact Ideal.subset_span (by rw [hS]; simp)
    · exact Ideal.subset_span (by rw [hS]; simp)
    · exact Ideal.subset_span (by rw [hS]; simp)

theorem absNorm_p2 (hn : n % 8 = 5) : Ideal.absNorm (p2Ideal5 n) = 2 := by
  have h := congrArg Ideal.absNorm (p2_sq hn)
  rw [map_mul, Ideal.absNorm_span_singleton] at h
  have h2 : (Algebra.norm ℤ (2 : 𝓞 (QNeg n))).natAbs = 4 := by
    have := normZ_natCast (n := n) 2
    simp only [Nat.cast_ofNat] at this
    rw [this]; norm_num
  rw [h2] at h
  have : Ideal.absNorm (p2Ideal5 n) * Ideal.absNorm (p2Ideal5 n) = 2 * 2 := h
  nlinarith [Nat.zero_le (Ideal.absNorm (p2Ideal5 n))]

theorem a_mul_p2 (hn : n % 8 = 5) : varpiIdeal n * p2Ideal5 n = Ideal.span {sqrtNeg n - 1} := by
  rw [varpiIdeal, p2Ideal5, Ideal.span_pair_mul_span_pair]
  have hv := varpi_sq_add n
  have hm : (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) * 2 = (n : 𝓞 (QNeg n)) + 1 := by
    have : (n + 1) / 2 * 2 = n + 1 := by omega
    exact_mod_cast this
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, Ideal.mem_span_singleton']
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨-(sqrtNeg n - 1) - 2, by linear_combination -hv - hm⟩
    · exact ⟨(((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)), by ring⟩
    · exact ⟨2, by ring⟩
    · exact ⟨sqrtNeg n - 1, rfl⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    set S : Set (𝓞 (QNeg n)) := {(((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) * 2,
      (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) * (sqrtNeg n - 1), (sqrtNeg n - 1) * 2,
      (sqrtNeg n - 1) * (sqrtNeg n - 1)} with hS
    have e : sqrtNeg n - 1 = 1 * ((((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) * (sqrtNeg n - 1)) -
        (((n + 1) / 4 : ℕ) : 𝓞 (QNeg n)) * ((sqrtNeg n - 1) * 2) := by
      have : (n + 1) / 2 = 2 * ((n + 1) / 4) + 1 := by omega
      have h' : (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) = 2 * (((n + 1) / 4 : ℕ) : 𝓞 (QNeg n)) + 1 := by
        exact_mod_cast this
      rw [h']; ring
    rw [e]
    refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
    · exact Ideal.subset_span (by rw [hS]; simp)
    · exact Ideal.subset_span (by rw [hS]; simp)

def pstar' (p : ℕ) : ℤ := if p % 4 = 1 then (p : ℤ) else -(p : ℤ)

omit [NeZero n] in
theorem odd_of_mem_primeFactors (hodd : Odd n) {q : ℕ} (hq : q ∈ n.primeFactors) : q % 2 = 1 := by
  have hqd := Nat.dvd_of_mem_primeFactors hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  rcases hqp.eq_two_or_odd with h | h
  · subst h; exact absurd (even_iff_two_dvd.2 hqd) (Nat.not_even_iff_odd.2 hodd)
  · exact h

omit [NeZero n] in
/-- `Π_{q ∣ n} (2/q) = (2/n) = −1` for squarefree `n ≡ 5 (mod 8)`. -/
theorem prod_sign_two (hn : n % 8 = 5) (hsq : Squarefree n) :
    ∏ q ∈ n.primeFactors, (if q % 8 = 1 ∨ q % 8 = 7 then (1 : ℤ) else -1) = -1 := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have h1 : ∀ q ∈ n.primeFactors, (if q % 8 = 1 ∨ q % 8 = 7 then (1 : ℤ) else -1) =
      ZMod.χ₈ (q : ZMod 8) := by
    intro q hq
    have hq2 := odd_of_mem_primeFactors hodd hq
    rw [ZMod.χ₈_nat_eq_if_mod_eight, if_neg (show ¬ (q % 2 = 0) by omega)]
  rw [Finset.prod_congr rfl h1, ← map_prod, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq,
    ZMod.χ₈_nat_eq_if_mod_eight, if_neg (show ¬ (n % 2 = 0) by omega),
    if_neg (show ¬ (n % 8 = 1 ∨ n % 8 = 7) by omega)]

omit [NeZero n] in
/-- `Π_{q ∣ n} q* = n` for squarefree `n ≡ 1 (mod 4)`. -/
theorem prod_pstar (hn : n % 4 = 1) (hsq : Squarefree n) :
    ∏ q ∈ n.primeFactors, pstar' q = n := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have h1 : ∀ q ∈ n.primeFactors, pstar' q = ZMod.χ₄ (q : ZMod 4) * (q : ℤ) := by
    intro q hq
    have hq2 := odd_of_mem_primeFactors hodd hq
    rw [ZMod.χ₄_nat_eq_if_mod_four, if_neg (show ¬ (q % 2 = 0) by omega)]
    unfold pstar'
    split_ifs <;> ring
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, ← map_prod, ← Nat.cast_prod, ← Nat.cast_prod,
    Nat.prod_primeFactors_of_squarefree hsq, ZMod.χ₄_nat_eq_if_mod_four,
    if_neg (show ¬ (n % 2 = 0) by omega), if_pos hn, one_mul]

theorem picClass_maximal' {K : Type} [Field K] [NumberField K]
    (J : integralIdealsPrimeTo (maximalNumberFieldOrder K).conductorModulus)
    (hJ : (J : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰) :
    (maximalNumberFieldOrder K).picClass J =
      (ClassGroup.mk0 ⟨(J : Ideal (𝓞 K)), hJ⟩ : ClassGroup (𝓞 K)) := by
  rw [picClass_apply, ← ClassGroup.mk_mk0 K]
  congr 1
  apply Units.ext
  rw [coe_integralIdealsAwayConductorToInvertible_apply, FractionalIdeal.coe_mk0]
  congr 1
  ext x
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨(⟨x.1, x.2⟩ : 𝓞 K), (maximalNumberFieldOrder K).mem_toRingOfIntegers.mpr x.2⟩, hx, rfl⟩

theorem picToMax_picClass {K : Type} [Field K] [NumberField K] (O : NumberFieldOrder K)
    (J : integralIdealsPrimeTo O.conductorModulus) (hJ : (J : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰) :
    picToMax O (O.picClass J) = (ClassGroup.mk0 ⟨(J : Ideal (𝓞 K)), hJ⟩ : ClassGroup (𝓞 K)) := by
  obtain ⟨t, ht⟩ := rayClassQuotient_surjective O.conductorModulus
    (idealClass O.conductorModulus J)
  have hQ : ringClassIdeleQuotient O t = O.picClass J := by
    rw [ringClassIdeleQuotient_apply, ht, rayClassToPic_idealClass]
  rw [← hQ, picToMax_ringClassIdeleQuotient, ringClassIdeleQuotient_apply,
    ← classMap_rayClassQuotient (maximal_conductorModulus_dvd O), ht, classMap_idealClass,
    rayClassToPic_idealClass]
  have hJ' : ((integralIdealsPrimeToInclusion (maximal_conductorModulus_dvd O) J :
      integralIdealsPrimeTo (maximalNumberFieldOrder K).conductorModulus) : Ideal (𝓞 K)) ∈
      (Ideal (𝓞 K))⁰ := by
    rw [coe_integralIdealsPrimeToInclusion]; exact hJ
  rw [picClass_maximal' _ hJ']
  congr 2

theorem span_two_ne_zero (x : 𝓞 (QNeg n)) : Ideal.span {2, x} ≠ 0 := by
  intro h0
  have h2 : (2 : 𝓞 (QNeg n)) ∈ Ideal.span {2, x} := Ideal.subset_span (by simp)
  rw [h0, Ideal.zero_eq_bot, Ideal.mem_bot] at h2
  exact two_ne_zero h2

theorem chi_wClass (hn : n % 8 = 5) (hsq : Squarefree n) (q : n.primeFactors) :
    chi n q (picToMax (O4 n) (wClass n)) = Multiplicative.ofAdd (ZInQ.RouteK.legBit q 2) := by
  sorry

theorem chi_test (hn : n % 8 = 5) (hsq : Squarefree n) (q : n.primeFactors) :
    chi n q (picToMax (O4 n) (wClass n)) = Multiplicative.ofAdd (ZInQ.RouteK.legBit q 2) := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have ha0 : varpiIdeal n ∈ (Ideal (𝓞 (QNeg n)))⁰ := mem_nonZeroDivisors_of_ne_zero (by
    rw [Ideal.zero_eq_bot]
    exact ((mem_integralIdealsPrimeTo_conductorModulus_iff (O4 n)).1 (varpiIdeal_mem hn)).1)
  rw [wClass_eq hn]
  sorry

end ZInQ.Contrib.TYZGenus.T321G
