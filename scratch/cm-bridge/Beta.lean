import ZInQKernel.Contrib.TYZGenus.RingClassBridge

/-! Development file for §13 of `Bridge.lean` (towards glue BETA-7). -/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.CMBridgeDev

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Package
  ZInQ.Contrib.TYZGenus.RingClass NumberField TauCeti.ClassFieldTheory
  TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder ZInQ.RouteK.Rank5b
  ZInQ.RouteK.Redei IsDedekindDomain
open scoped nonZeroDivisors

/-- `p* = (−1)^{(p−1)/2} p` for odd `p`. -/
def pstar (p : ℕ) : ℤ := if p % 4 = 1 then (p : ℤ) else -(p : ℤ)

/-- **Quadratic reciprocity, finite-field form with `p*`**: in a finite field `F` of odd
characteristic `≠ p`, `p*` is a square iff `|F|` is a square mod `p`. -/
theorem isSquare_pstar_iff {F : Type*} [Field F] [Fintype F] (hF : ringChar F ≠ 2) {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) (hpF : ringChar F ≠ p) :
    IsSquare ((pstar p : ℤ) : F) ↔ IsSquare ((Fintype.card F : ℕ) : ZMod p) := by
  classical
  obtain ⟨k, hk, hcard⟩ := FiniteField.card F (ringChar F)
  have hpF0 : ((p : ℕ) : F) ≠ 0 := by
    intro h
    exact hpF ((Nat.prime_dvd_prime_iff_eq hk hp.out).1 ((ringChar.spec F p).1 h))
  have hq0 : ((Fintype.card F : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    rw [hcard] at hd
    exact hpF ((Nat.prime_dvd_prime_iff_eq hp.out hk).1 (hp.out.dvd_of_dvd_pow hd)).symm
  have hodd := FiniteField.odd_card_of_char_ne_two hF
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by
    have := hp.out.eq_one_or_self_of_dvd 2
    rcases Nat.even_or_odd p with he | ho
    · exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).1 (even_iff_two_dvd.1 he)).symm hp2
    · omega
  have hq4 : Fintype.card F % 4 = 1 ∨ Fintype.card F % 4 = 3 := by omega
  have hχp : quadraticChar (ZMod p) (-1) = ZMod.χ₄ p := by
    rw [quadraticChar_neg_one (by rwa [ZMod.ringChar_zmod_n]), ZMod.card]
  have key : quadraticChar F ((pstar p : ℤ) : F) = quadraticChar (ZMod p) (Fintype.card F) := by
    have hodd' := quadraticChar_odd_prime hF hp2 hpF
    unfold pstar
    rcases hp4 with h | h
    · rw [if_pos h, Int.cast_natCast, hodd', map_mul]
      rcases hq4 with hq | hq
      · rw [ZMod.χ₄_nat_one_mod_four hq]; simp
      · rw [ZMod.χ₄_nat_three_mod_four hq, Int.cast_neg, Int.cast_one, hχp,
          ZMod.χ₄_nat_one_mod_four h, one_mul]
    · rw [if_neg (by omega), Int.cast_neg, Int.cast_natCast, neg_eq_neg_one_mul, map_mul, hodd',
        map_mul, quadraticChar_neg_one hF]
      rcases hq4 with hq | hq
      · rw [ZMod.χ₄_nat_one_mod_four hq]; simp
      · rw [ZMod.χ₄_nat_three_mod_four hq, Int.cast_neg, Int.cast_one, hχp,
          ZMod.χ₄_nat_three_mod_four h]; ring
  have hps0 : ((pstar p : ℤ) : F) ≠ 0 := by
    unfold pstar; split_ifs <;> simpa using hpF0
  rw [← quadraticChar_one_iff_isSquare hps0, ← quadraticChar_one_iff_isSquare hq0, key]


section Star

variable {n : ℕ} [NeZero n]

/-- `{p* : p ∣ n}`. -/
def pstarSet (n : ℕ) : Finset ℤ := n.primeFactors.image pstar

/-- `K_n(√p* : p ∣ n) ⊆ K_nˢ` (the genus field, `genusField_le_genusStar`). -/
def genusStar (n : ℕ) [NeZero n] : IntermediateField (QNeg n) (SeparableClosure (QNeg n)) :=
  IntermediateField.adjoin (QNeg n) (sqrtK (QNeg n) '' (pstarSet n : Set ℤ))

theorem adjSqrt_le_genusStar {a : ℤ} (ha : a ∈ pstarSet n) : adjSqrt (QNeg n) a ≤ genusStar n :=
  IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.2
    (Set.mem_image_of_mem _ (Finset.mem_coe.2 ha)))

instance : FiniteDimensional (QNeg n) (genusStar n) :=
  IntermediateField.finiteDimensional_adjoin fun x hx => by
    obtain ⟨a, -, rfl⟩ := hx
    exact isIntegral_sqrtK _ a

instance : Normal (QNeg n) (genusStar n) := by
  rw [IntermediateField.normal_iff_forall_map_le']
  intro g
  rw [genusStar, IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, ha, rfl⟩ := hx
  have h : g (sqrtK (QNeg n) a) ^ 2 = sqrtK (QNeg n) a ^ 2 := by
    rw [← map_pow, sqrtK_sq, map_intCast]
  have hmem : sqrtK (QNeg n) a ∈ genusStar n :=
    IntermediateField.subset_adjoin _ _ (Set.mem_image_of_mem _ ha)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · simp only [AlgEquiv.coe_toAlgHom, h, SetLike.mem_coe]; exact hmem
  · simp only [AlgEquiv.coe_toAlgHom, h, SetLike.mem_coe]; exact neg_mem hmem

instance : IsGalois (QNeg n) (genusStar n) := IsGalois.mk

theorem pstar_mem_or (p : ℕ) : pstar p = p ∨ pstar p = -p := by
  unfold pstar; split_ifs <;> simp

/-- The residue field at `𝔭 ∌ 2n` has characteristic `≠ 2` and `≠ p` for `p ∣ n`. -/
theorem residue_facts (𝔭 : HeightOneSpectrum (𝓞 (QNeg n)))
    (h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal) {p : ℕ} (hp : p ∈ n.primeFactors) :
    letI := Ideal.Quotient.field 𝔭.asIdeal
    ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) ≠ 2 ∧ ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) ≠ p := by
  letI := Ideal.Quotient.field 𝔭.asIdeal
  have hmem : ∀ k : ℕ, k ∣ 2 * n → ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) ≠ k := by
    intro k hk hc
    apply h2n
    obtain ⟨m, hm⟩ := hk
    have h0 : ((k : ℕ) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal) = 0 := by rw [← hc]; exact ringChar.Nat.cast_ringChar
    have h1 : ((k : ℕ) : 𝓞 (QNeg n)) ∈ 𝔭.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]; simpa using h0
    rw [show ((2 * n : ℕ) : 𝓞 (QNeg n)) = ((k * m : ℕ) : 𝓞 (QNeg n)) from congrArg _ hm, Nat.cast_mul]
    exact 𝔭.asIdeal.mul_mem_right _ h1
  exact ⟨hmem 2 ⟨n, rfl⟩, hmem p (Dvd.dvd.mul_left (Nat.dvd_of_mem_primeFactors hp) 2)⟩

/-- Genus characters at a prime split in `K_n(√p* : p ∣ n)`. -/
theorem chi_eq_one_of_isSquare_pstar (hn : Odd n) (hsq : Squarefree n)
    (𝔭 : HeightOneSpectrum (𝓞 (QNeg n)))
    (h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal)
    (hp : ∀ p ∈ n.primeFactors, IsSquare (((pstar p : ℤ) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal)))
    (q : n.primeFactors) :
    chi n q (ClassGroup.mk0 ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩) = 1 := by
  have hqp := Nat.prime_of_mem_primeFactors q.2
  have := Fact.mk hqp
  letI := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
  letI := Fintype.ofFinite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal)
  obtain ⟨hchar, hcharq⟩ := residue_facts 𝔭 h2n q.2
  have hq2 : (q : ℕ) ≠ 2 := by
    rintro h
    have := Nat.dvd_of_mem_primeFactors q.2
    rw [h] at this
    exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 this)
  have hN : Ideal.absNorm 𝔭.asIdeal = Fintype.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hsquare := (isSquare_pstar_iff hchar hq2 hcharq).1 (hp q q.2)
  have hqN : ¬ (q : ℕ) ∣ Ideal.absNorm 𝔭.asIdeal := by
    rw [hN]
    intro hd
    obtain ⟨k, hk, hcard⟩ := FiniteField.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) (ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal))
    rw [hcard] at hd
    exact hcharq ((Nat.prime_dvd_prime_iff_eq hqp hk).1 (hqp.dvd_of_dvd_pow hd)).symm
  have hb : ZInQ.RouteK.legBit q ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ℤ) = 0 := by
    unfold ZInQ.RouteK.legBit
    rw [if_pos]
    rw [hN, Int.cast_natCast]
    exact hsquare
  have hc := chi_mk0 n hn hsq q ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩ hqN
  rw [hc, hb]
  rfl

end Star


section SqrtH

variable {n : ℕ} [NeZero n]

/-- Norms in `𝓞_{K_n}`, `n ≡ 3 (mod 4)` squarefree, `p ∣ n`: `4N(β) ≡ t² (mod p)`. -/
theorem norm_sq_mod_prime3 (hsq : Squarefree n) {p : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (β : 𝓞 (QNeg n)) : ∃ t : ℤ, (p : ℤ) ∣ 4 * Algebra.norm ℤ β - t ^ 2 := by
  obtain ⟨s, hs⟩ := exists_two_re β
  obtain ⟨m, hm⟩ := exists_two_re (β * sqrtNeg n)
  have hN := normZ_eq_re_im β
  have hre : ((β * sqrtNeg n : 𝓞 (QNeg n)) : QNeg n).re = -(n : ℚ) * (β : QNeg n).im := by
    simp [RingOfIntegers.coe_eq_algebraMap, coe_sqrtNeg]
  rw [hre] at hm
  refine ⟨s, ?_⟩
  set w := 4 * Algebra.norm ℤ β - s ^ 2
  have hw : (n : ℤ) * w = m ^ 2 := by
    have : ((n : ℤ) * w : ℚ) = (m : ℚ) ^ 2 := by
      simp only [w]; push_cast
      rw [hN, ← hs, ← hm]; ring
    exact_mod_cast this
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  obtain ⟨n', hn'⟩ := hpn
  have hpn' : ¬ (p : ℤ) ∣ n' := by
    intro h
    obtain ⟨k, rfl⟩ := Int.natCast_dvd_natCast.1 h
    have := hsq p ⟨k, by rw [hn']; ring⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.1 this)
  have hpm : (p : ℤ) ∣ m := by
    apply hpZ.dvd_of_dvd_pow (n := 2)
    rw [← hw, hn']; push_cast
    exact ⟨n' * w, by ring⟩
  obtain ⟨m', rfl⟩ := hpm
  have h2 : (p : ℤ) * (n' * w) = (p : ℤ) * (p * m' ^ 2) := by
    rw [hn'] at hw; push_cast at hw; linear_combination hw
  have h3 : (n' : ℤ) * w = p * m' ^ 2 := mul_left_cancel₀ hpZ.ne_zero h2
  have h4 : (p : ℤ) ∣ n' * w := ⟨m' ^ 2, h3⟩
  rcases hpZ.dvd_or_dvd h4 with h | h
  · exact absurd h hpn'
  · exact h

/-- **Genus theory, `n ≡ 3 (mod 4)`**: `K_n(√p*) ⊆ H_n` for every prime `p ∣ n` (Bauer: a principal
prime `𝔭 = β𝓞_K ∤ 2n` has `4N𝔭 ≡ t² (mod p)`, so `p*` is a square mod `𝔭` by `isSquare_pstar_iff`). -/
theorem adjSqrt_pstar_le_hilbertField (hn : n % 4 = 3) (hsq : Squarefree n) {p : ℕ}
    (hp : p ∈ n.primeFactors) :
    adjSqrt (QNeg n) (pstar p) ≤ hilbertField n := by
  rw [hilbertField_eq_ringSubfield]
  have hI : (conductorOrder (QNeg n) 1).conductor * Ideal.span {((2 * n : ℕ) : 𝓞 (QNeg n))} ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    refine ⟨(conductorOrder (QNeg n) 1).conductor_ne_bot, ?_⟩
    rw [Ideal.span_singleton_eq_bot]
    exact_mod_cast (show 2 * n ≠ 0 by have := NeZero.ne n; omega)
  refine le_of_splitSet_diff_subset _ (finite_le_primes _ hI) ?_
  rintro 𝔭 ⟨h𝔭, hT⟩
  have hT1 : ¬ (conductorOrder (QNeg n) 1).conductor ≤ 𝔭.asIdeal :=
    fun h => hT (le_trans Ideal.mul_le_left h)
  have h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := fun h =>
    hT (le_trans Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h))
  have hJ := mem_primeTo_of_not_le 𝔭 hT1
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (conductorOrder (QNeg n) 1).conductorModulus) :
    Ideal (𝓞 (QNeg n))).IsMaximal := 𝔭.isMaximal
  have h1 := (mem_splitSet_iff (conductorOrder (QNeg n) 1) ⊥ ⟨_, hJ⟩ 𝔭 rfl).1 h𝔭
  rw [Subgroup.mem_bot, picClass_eq_one_iff] at h1
  obtain ⟨β, -, hspan⟩ := h1
  have hq : Nat.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) = (Algebra.norm ℤ β).natAbs := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    change Ideal.absNorm (((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo
      (conductorOrder (QNeg n) 1).conductorModulus) : Ideal (𝓞 (QNeg n)))) = _
    rw [hspan, Ideal.absNorm_span_singleton]
  have hnn := normZ_nonneg (n := n) β
  have hc : ((Algebra.norm ℤ β).natAbs : ℤ) = Algebra.norm ℤ β := Int.natAbs_of_nonneg hnn
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨m, hm⟩ := Nat.dvd_of_mem_primeFactors hp
    omega
  haveI := Fact.mk hpp
  have h2a : ((2 * pstar p : ℤ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := by
    intro h; apply h2n
    obtain ⟨n', hn'⟩ := Nat.dvd_of_mem_primeFactors hp
    have e2 : 2 * n = 2 * p * n' := by rw [hn']; ring
    have hcast : ((2 * n : ℕ) : 𝓞 (QNeg n)) =
        ((2 * pstar p : ℤ) : 𝓞 (QNeg n)) * ((if p % 4 = 1 then 1 else -1 : ℤ) * n' : 𝓞 (QNeg n)) := by
      rw [congrArg (Nat.cast (R := 𝓞 (QNeg n))) e2]
      unfold pstar
      split_ifs <;> push_cast <;> ring
    rw [hcast]
    exact 𝔭.asIdeal.mul_mem_right _ h
  rw [mem_splitSet_adjSqrt_iff 𝔭 h2a]
  letI := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
  letI := Fintype.ofFinite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal)
  obtain ⟨hchar, hcharp⟩ := residue_facts 𝔭 h2n hp
  rw [isSquare_pstar_iff hchar hp2 hcharp]
  have hcard : Fintype.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) = (Algebra.norm ℤ β).natAbs := by
    rw [← Nat.card_eq_fintype_card, hq]
  rw [hcard]
  obtain ⟨t, ht⟩ := norm_sq_mod_prime3 hsq hpp (Nat.dvd_of_mem_primeFactors hp) β
  set N : ZMod p := (((Algebra.norm ℤ β).natAbs : ℕ) : ZMod p)
  have h4 : (4 : ZMod p) * N = (t : ZMod p) ^ 2 := by
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 ht
    have hN : N = ((Algebra.norm ℤ β : ℤ) : ZMod p) := by
      simp only [N]; rw [← Int.cast_natCast, hc]
    rw [hN]
    push_cast at h0
    linear_combination h0
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 h')
  have e : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  exact ⟨t * 2⁻¹, by linear_combination (2⁻¹ * 2⁻¹ : ZMod p) * h4 + (-N * (1 + 2 * 2⁻¹)) * e⟩

end SqrtH

end ZInQ.Contrib.TYZGenus.CMBridgeDev
