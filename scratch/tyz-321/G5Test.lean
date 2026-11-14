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


/-! ### The kernel of `Pic(O_{n,4}) → Cl(K_n)` -/

section Ker

open QuadraticAlgebra

/-- `u + v√−n ∈ 𝓞_K`. -/
abbrev elt (n : ℕ) [NeZero n] (u v : ℤ) : 𝓞 (QNeg n) := (u : 𝓞 (QNeg n)) + (v : 𝓞 (QNeg n)) * sqrtNeg n

theorem coe_elt (u v : ℤ) : ((elt n u v : 𝓞 (QNeg n)) : QNeg n) = ⟨u, v⟩ := by
  simp only [elt]; push_cast [coe_sqrtNeg]; ext <;> simp

theorem eq_elt (hn4 : n % 4 = 1) (hsq : Squarefree n) (y : 𝓞 (QNeg n)) :
    ∃ u v : ℤ, y = elt n u v := by
  obtain ⟨u, v, hu, hv⟩ := Shimura.int_coords hn4 hsq y
  refine ⟨u, v, RingOfIntegers.ext ?_⟩
  rw [coe_elt]; ext <;> simp [hu, hv]

theorem elt_mul_conj (u v : ℤ) : elt n u v * elt n u (-v) = ((u ^ 2 + n * v ^ 2 : ℤ) : 𝓞 (QNeg n)) := by
  simp only [elt]; push_cast
  linear_combination (-(v : 𝓞 (QNeg n)) ^ 2) * sqrtNeg_mul_self (d := n)

theorem mem_O4_elt (a : ℤ) (z : 𝓞 (QNeg n)) : (a : 𝓞 (QNeg n)) + 4 * z ∈ (O4 n).toRingOfIntegers := by
  rw [NumberFieldOrder.mem_toRingOfIntegers, Shimura.mem_O4_iff']
  refine ⟨a, z, ?_⟩
  simp only [map_add, map_mul, map_intCast, map_ofNat]

theorem odd_norm {n : ℕ} (hn : n % 2 = 1) {u v : ℤ} (huv : (u + v) % 2 = 1) :
    ∃ M : ℤ, u ^ 2 + n * v ^ 2 = 2 * M + 1 := by
  rcases Int.emod_two_eq_zero_or_one u with hu | hu
  · obtain ⟨a, rfl⟩ : ∃ a, u = 2 * a := ⟨u / 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, v = 2 * b + 1 := ⟨v / 2, by omega⟩
    obtain ⟨c, hc⟩ : ∃ c, (n : ℤ) = 2 * c + 1 := ⟨n / 2, by omega⟩
    exact ⟨2 * a ^ 2 + (2 * c + 1) * (2 * b ^ 2 + 2 * b) + c, by rw [hc]; ring⟩
  · obtain ⟨a, rfl⟩ : ∃ a, u = 2 * a + 1 := ⟨u / 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, v = 2 * b := ⟨v / 2, by omega⟩
    exact ⟨2 * a ^ 2 + 2 * a + 2 * n * b ^ 2, by ring⟩

/-- `(u + v√−n)` with `u + v` odd is prime to the conductor of `O_{n,4}`. -/
theorem span_elt_mem (hn : n % 8 = 5) {u v : ℤ} (huv : (u + v) % 2 = 1) :
    Ideal.span {elt n u v} ∈ integralIdealsPrimeTo (O4 n).conductorModulus := by
  rw [mem_integralIdealsPrimeTo_conductorModulus_iff]
  obtain ⟨M, hM⟩ := odd_norm (n := n) (by omega) huv
  have hN := elt_mul_conj (n := n) u v
  refine ⟨?_, ?_⟩
  · intro h
    have hx : elt n u v ∈ Ideal.span {elt n u v} := Ideal.subset_span rfl
    rw [h, Ideal.mem_bot] at hx
    rw [hx, zero_mul, hM] at hN
    have h1 : (((2 * M + 1 : ℤ)) : 𝓞 (QNeg n)) = ((0 : ℤ) : 𝓞 (QNeg n)) := by
      rw [← hN]; simp
    have := intCast_injective (n := n) h1
    omega
  · rw [Ideal.eq_top_iff_one]
    -- 1 = x * (x̄ * (2M+1)) - 4 * (M * (M + 1))
    have e : (1 : 𝓞 (QNeg n)) = elt n u v * (elt n u (-v) * ((2 * M + 1 : ℤ) : 𝓞 (QNeg n))) +
        4 * ((-(M * (M + 1)) : ℤ) : 𝓞 (QNeg n)) := by
      rw [← mul_assoc, hN, hM]; push_cast; ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)))
      (Ideal.mem_sup_right ?_)
    simpa using natCast_mul_mem_conductor (QNeg n) 4 (((-(M * (M + 1)) : ℤ)) : 𝓞 (QNeg n))

/-- **Congruence lemma**: if `x ≡ a·y (mod 4𝓞_K)`, `a ∈ ℤ`, then `[x ∩ O] = [y ∩ O]` in `Pic(O_{n,4})`. -/
theorem picClass_congr (hn : n % 8 = 5) {u v u' v' : ℤ} (huv : (u + v) % 2 = 1)
    (huv' : (u' + v') % 2 = 1) (a : ℤ) (z : 𝓞 (QNeg n))
    (h : elt n u v = a * elt n u' v' + 4 * z) :
    (O4 n).picClass ⟨_, span_elt_mem hn huv⟩ = (O4 n).picClass ⟨_, span_elt_mem hn huv'⟩ := by
  have huv'' : (u' + -v') % 2 = 1 := by omega
  have hb := span_elt_mem hn huv''
  have hN := elt_mul_conj (n := n) u' v'
  -- `[x][ȳ] = 1` and `[y][ȳ] = 1`
  have hprod : ∀ {x : 𝓞 (QNeg n)} (hx : Ideal.span {x} ∈ integralIdealsPrimeTo (O4 n).conductorModulus)
      (hxy : x * elt n u' (-v') ∈ (O4 n).toRingOfIntegers),
      (O4 n).picClass ⟨_, hx⟩ * (O4 n).picClass ⟨_, hb⟩ = 1 := by
    intro x hx hxy
    rw [← map_mul]
    have hm : (⟨_, hx⟩ : integralIdealsPrimeTo (O4 n).conductorModulus) * ⟨_, hb⟩ =
        ⟨Ideal.span {x * elt n u' (-v')}, by
          rw [← Ideal.span_singleton_mul_span_singleton]; exact Submonoid.mul_mem _ hx hb⟩ :=
      Subtype.ext (Ideal.span_singleton_mul_span_singleton _ _)
    rw [hm, picClass_eq_one_iff]
    exact ⟨_, hxy, rfl⟩
  have h1 := hprod (span_elt_mem hn huv) (by
    rw [h, add_mul, mul_assoc, hN, ← Int.cast_mul, mul_assoc]
    exact mem_O4_elt _ _)
  have h2 := hprod (span_elt_mem hn huv') (by
    rw [hN]
    have := mem_O4_elt (n := n) (u' ^ 2 + n * v' ^ 2) 0
    rwa [mul_zero, add_zero] at this)
  exact mul_right_cancel (h1.trans h2.symm)

end Ker

section Ker2
open QuadraticAlgebra

theorem elt_mem_p2 {u v : ℤ} (huv : (u + v) % 2 = 0) : elt n u v ∈ p2Ideal5 n := by
  obtain ⟨t, ht⟩ : ∃ t, u + v = 2 * t := ⟨(u + v) / 2, by omega⟩
  have e : elt n u v = (t : 𝓞 (QNeg n)) * 2 + (v : 𝓞 (QNeg n)) * (sqrtNeg n - 1) := by
    simp only [elt]
    have : (u : 𝓞 (QNeg n)) = 2 * t - v := by
      have h' : ((u : ℤ) : 𝓞 (QNeg n)) = ((2 * t - v : ℤ) : 𝓞 (QNeg n)) := by rw [← ht]; ring_nf
      push_cast at h'; exact h'
    rw [this]; ring
  rw [e, p2Ideal5]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

theorem conductor_le_p2 (hn : n % 8 = 5) (hsq : Squarefree n) : (O4 n).conductor ≤ p2Ideal5 n := by
  have hn4 : n % 4 = 1 := by omega
  intro c hc
  rw [NumberFieldOrder.mem_conductor_iff] at hc
  have h1 := hc 1
  have h2 := hc (sqrtNeg n)
  rw [Shimura.mem_O4_iff'] at h1 h2
  obtain ⟨a, y, hy⟩ := h1
  obtain ⟨a', y', hy'⟩ := h2
  obtain ⟨y1, y2, hy1, hy2⟩ := Shimura.int_coords hn4 hsq y
  obtain ⟨y1', y2', hy1', hy2'⟩ := Shimura.int_coords hn4 hsq y'
  rw [show ((1 : 𝓞 (QNeg n)) : QNeg n) = 1 from rfl, mul_one] at hy
  rw [hy, coe_sqrtNeg] at hy'
  have him := congrArg QuadraticAlgebra.im hy'
  simp [hy1, hy2, hy1', hy2'] at him
  have ha : (a : ℚ) = 4 * (y2' - y1) := by linarith
  have ha' : a = 4 * (y2' - y1) := by exact_mod_cast ha
  have e : c = 2 * (2 * (((y2' - y1 : ℤ) : 𝓞 (QNeg n)) + y)) := by
    apply RingOfIntegers.ext
    have hcI : ∀ m : ℤ, ((m : 𝓞 (QNeg n)) : QNeg n) = m := fun m =>
      map_intCast (algebraMap (𝓞 (QNeg n)) (QNeg n)) m
    rw [hy, ha']; push_cast [Shimura.coeO_two, hcI]; ring
  rw [e, p2Ideal5]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem p2_ne_top (hn : n % 8 = 5) : p2Ideal5 n ≠ ⊤ := by
  intro h
  have := absNorm_p2 (n := n) hn
  rw [h, Ideal.absNorm_top] at this
  omega

/-- A principal ideal `(u + v√−n)` prime to the conductor has `u + v` odd. -/
theorem odd_of_mem (hn : n % 8 = 5) (hsq : Squarefree n) {u v : ℤ}
    (h : Ideal.span {elt n u v} ∈ integralIdealsPrimeTo (O4 n).conductorModulus) :
    (u + v) % 2 = 1 := by
  by_contra hc
  have hc' : (u + v) % 2 = 0 := by omega
  rw [mem_integralIdealsPrimeTo_conductorModulus_iff] at h
  apply p2_ne_top hn
  rw [eq_top_iff, ← h.2]
  exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 (elt_mem_p2 hc')) (conductor_le_p2 hn hsq)

end Ker2

section Ker3
open QuadraticAlgebra

theorem elt_lin (a u' v' s t : ℤ) :
    (a : 𝓞 (QNeg n)) * elt n u' v' + 4 * elt n s t = elt n (a * u' + 4 * s) (a * v' + 4 * t) := by
  simp only [elt]; push_cast; ring

theorem elt_mul (u v u' v' : ℤ) :
    elt n u v * elt n u' v' = elt n (u * u' - n * v * v') (u * v' + v * u') := by
  simp only [elt]; push_cast
  linear_combination ((v : 𝓞 (QNeg n)) * v') * sqrtNeg_mul_self (d := n)

theorem pic_one (hn : n % 8 = 5) :
    (O4 n).picClass ⟨_, span_elt_mem (n := n) hn (u := 1) (v := 0) (by decide)⟩ = 1 := by
  rw [picClass_eq_one_iff]
  refine ⟨elt n 1 0, ?_, rfl⟩
  simpa [elt] using mem_O4_elt (n := n) 1 0

theorem pic_sigma (hn : n % 8 = 5) :
    (O4 n).picClass ⟨_, span_elt_mem (n := n) hn (u := 1) (v := 2) (by decide)⟩ = sigmaClass n := by
  rw [sigmaClass_eq]
  have e : alpha n = elt n 3 2 := by simp only [alpha, elt]; push_cast; ring
  have h1 : (O4 n).picClass ⟨_, alphaIdeal_mem⟩ =
      (O4 n).picClass ⟨_, span_elt_mem (n := n) hn (u := 3) (v := 2) (by decide)⟩ := by
    congr 1 <;> simp [e]
  rw [h1]
  exact (picClass_congr hn (u := 3) (v := 2) (u' := 1) (v' := 2) (by decide) (by decide) (-1)
    (elt n 1 1) (by rw [elt_lin]; norm_num)).symm

theorem varpi_sq (k : ℕ) (hk : n = 8 * k + 5) :
    (sqrtNeg n - 1) * (sqrtNeg n - 1) = 2 * elt n (-4 * k - 2) (-1) := by
  have hk' : (n : 𝓞 (QNeg n)) = 8 * (k : 𝓞 (QNeg n)) + 5 := by
    have := congrArg (Nat.cast (R := 𝓞 (QNeg n))) hk
    push_cast at this; exact this
  simp only [elt]; push_cast
  linear_combination sqrtNeg_mul_self (d := n) - hk'

theorem a_sq (hn : n % 8 = 5) (k : ℕ) (hk : n = 8 * k + 5) :
    varpiIdeal n * varpiIdeal n = Ideal.span {elt n (-4 * k - 2) (-1)} := by
  have h2 : (Ideal.span {(2 : 𝓞 (QNeg n))}) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact two_ne_zero
  apply mul_right_cancel₀ h2
  rw [← p2_sq hn]
  calc varpiIdeal n * varpiIdeal n * (p2Ideal5 n * p2Ideal5 n)
      = (varpiIdeal n * p2Ideal5 n) * (varpiIdeal n * p2Ideal5 n) := by ring
    _ = Ideal.span {(sqrtNeg n - 1) * (sqrtNeg n - 1)} := by
        rw [a_mul_p2 hn, Ideal.span_singleton_mul_span_singleton]
    _ = _ := by
        rw [varpi_sq k hk, ← Ideal.span_singleton_mul_span_singleton, mul_comm, p2_sq hn]

theorem pic_w2 (hn : n % 8 = 5) :
    (O4 n).picClass ⟨_, span_elt_mem (n := n) hn (u := 2) (v := 1) (by decide)⟩ = wClass n ^ 2 := by
  have hb : ((-4 * ((n / 8 : ℕ) : ℤ) - 2) + -1) % 2 = 1 := by omega
  have hk : n = 8 * (n / 8) + 5 := by omega
  rw [wClass_eq hn, ← map_pow]
  have h1 : (⟨_, varpiIdeal_mem hn⟩ : integralIdealsPrimeTo (O4 n).conductorModulus) ^ 2 =
      ⟨_, span_elt_mem hn hb⟩ := Subtype.ext (by
        show varpiIdeal n ^ 2 = _
        rw [pow_two, a_sq hn (n / 8) hk])
  rw [h1]
  exact (picClass_congr hn (u' := 2) (v' := 1) hb (by decide) (-1) (elt n (-((n / 8 : ℕ) : ℤ)) 0)
    (by rw [elt_lin]; congr 1 <;> ring)).symm

theorem pic_omega (hn : n % 8 = 5) :
    (O4 n).picClass ⟨_, span_elt_mem (n := n) hn (u := 0) (v := 1) (by decide)⟩ =
      sigmaClass n * wClass n ^ 2 := by
  have hb : ((1 * 2 - (n : ℤ) * 2 * 1) + (1 * 1 + 2 * 2)) % 2 = 1 := by omega
  rw [← pic_sigma hn, ← pic_w2 hn, ← map_mul]
  have h1 : (⟨_, span_elt_mem (n := n) hn (u := 1) (v := 2) (by decide)⟩ :
      integralIdealsPrimeTo (O4 n).conductorModulus) *
        ⟨_, span_elt_mem (n := n) hn (u := 2) (v := 1) (by decide)⟩ =
      ⟨_, span_elt_mem hn hb⟩ := Subtype.ext (by
        show Ideal.span _ * Ideal.span _ = _
        rw [Ideal.span_singleton_mul_span_singleton, elt_mul])
  rw [h1]
  exact (picClass_congr hn (u' := 0) (v' := 1) hb (by decide) 1 (elt n (-4 * (n / 8 : ℕ) - 2) 1)
    (by rw [elt_lin]; congr 1 <;> omega)).symm

/-- **The kernel of `Pic(O_{n,4}) → Cl(K_n)` is `{1, σ, w², σw²}`** (for `n ≡ 5 (mod 8)`). -/
theorem ker_cases (hn : n % 8 = 5) (hsq : Squarefree n) {k : Pic (O4 n)}
    (hk : picToMax (O4 n) k = 1) :
    k = 1 ∨ k = sigmaClass n ∨ k = wClass n ^ 2 ∨ k = sigmaClass n * wClass n ^ 2 := by
  have hn4 : n % 4 = 1 := by omega
  obtain ⟨J, rfl⟩ := (O4 n).picClass_surjective k
  have hJ0 : (J : Ideal (𝓞 (QNeg n))) ∈ (Ideal (𝓞 (QNeg n)))⁰ := mem_nonZeroDivisors_of_ne_zero (by
    rw [Ideal.zero_eq_bot]
    exact ((mem_integralIdealsPrimeTo_conductorModulus_iff (O4 n)).1 J.2).1)
  rw [picToMax_picClass (O4 n) J hJ0] at hk
  have hk' : (ClassGroup.mk0 ⟨(J : Ideal (𝓞 (QNeg n))), hJ0⟩ : ClassGroup (𝓞 (QNeg n))) = 1 := hk
  rw [ClassGroup.mk0_eq_one_iff] at hk'
  obtain ⟨⟨x, hx⟩⟩ := hk'
  obtain ⟨u, v, rfl⟩ := eq_elt hn4 hsq x
  have hmem : Ideal.span {elt n u v} ∈ integralIdealsPrimeTo (O4 n).conductorModulus := by
    have := J.2; rw [show (J : Ideal (𝓞 (QNeg n))) = Ideal.span {elt n u v} from hx] at this
    exact this
  have huv := odd_of_mem hn hsq hmem
  have hJ : J = ⟨_, span_elt_mem hn huv⟩ := Subtype.ext hx
  rw [hJ]
  rcases (by omega : v % 4 = 0 ∨ v % 4 = 2 ∨ (v % 2 = 1 ∧ u % 4 = 0) ∨ (v % 2 = 1 ∧ u % 4 = 2))
    with h | h | h | h
  · left
    rw [picClass_congr hn huv (u' := 1) (v' := 0) (by decide) u (elt n 0 (v / 4)) (by rw [elt_lin]; congr 1 <;> omega),
      pic_one hn]
  · right; left
    rw [picClass_congr hn huv (u' := 1) (v' := 2) (by decide) u (elt n 0 ((v - 2 * u) / 4))
      (by rw [elt_lin]; congr 1 <;> omega), pic_sigma hn]
  · right; right; right
    rw [picClass_congr hn huv (u' := 0) (v' := 1) (by decide) v (elt n (u / 4) 0) (by rw [elt_lin]; congr 1 <;> omega),
      pic_omega hn]
  · right; right; left
    rw [picClass_congr hn huv (u' := 2) (v' := 1) (by decide) v (elt n ((u - 2 * v) / 4) 0)
      (by rw [elt_lin]; congr 1 <;> omega), pic_w2 hn]

end Ker3

end ZInQ.Contrib.TYZGenus.T321G
