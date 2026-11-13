import ZInQKernel.Contrib.TYZGenus.RingClassTwo

/-!
# The genus field explicitly: `L_n(i) ⊆ H_n` (task ring-class)

For squarefree `n ≡ 1 (mod 4)`, `K_n = ℚ(√−n)` (discriminant `−4n`):

* `adjSqrt_le_hilbertField`: `K_n(√−1)` and `K_n(√p)`, `p ∣ n` prime, lie in the Hilbert class
  field `H_n` (genus theory; Cox, *Primes of the form x² + ny²*, Theorem 6.1, UNVERIFIED numbering).
  Proof: Bauer's theorem (`le_of_splitSet_diff_subset`, from Tau Ceti's Chebotarev theorem), the
  splitting law in `K(√a)` (`mem_splitSet_adjSqrt_iff`), the norm form `N(β) = t² + w`, `k² = 4nw`
  (`norm_eq_sq_add`), and quadratic reciprocity in Mathlib's form `FiniteField.isSquare_odd_prime_iff`.
* `Lni_le_Hprimebar`: `L_n(i) = ℚ(i, √p : p ∣ n) ⊆ H'_n` (TYZ L1322's field inside TYZ's `H'_n`).
* `HHprime_eq_iSup`: for squarefree `n ≡ 5 (mod 8)`, `ℍ'_n = Π_{d₀ ∣ n, d₀ ≡ 5 (8)} H'_{d₀}`: the factor
  `L_n(i)` in TYZ's definition of `ℍ'_n` (L1320) is redundant.
-/

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory IsDedekindDomain Polynomial

noncomputable section
namespace ZInQ.Contrib.TYZGenus.RingClass

section GenusFieldExplicit

open ZInQ.RouteK.Rank5b ZInQ.RouteK.Redei ZInQ.Contrib.TYZDecomp.CurveA

variable {n : ℕ} [NeZero n]

theorem conductorOrder_one (K : Type) [Field K] [NumberField K] :
    conductorOrder K 1 = maximalNumberFieldOrder K := by
  ext x
  constructor
  · intro hx; exact conductorOrderSubalgebra_le_integralClosure K 1 hx
  · intro hx
    exact ⟨0, ⟨x, hx⟩, by simp only [Int.cast_zero, zero_add, Nat.cast_one, one_mul]; rfl⟩

theorem hilbertField_eq_ringSubfield :
    hilbertField n = ringSubfield (⊥ : Subgroup (Pic (conductorOrder (QNeg n) 1))) := by
  rw [← ringClassField_eq_ringSubfield, conductorOrder_one]

/-- Norms in `𝓞_{K_n}`, `n ≡ 1 (mod 4)`: `N(β) = t² + w` with `k² = 4nw` (`t = re β`,
`k = −2n im β`). -/
theorem norm_eq_sq_add (hn : n % 4 = 1) (β : 𝓞 (QNeg n)) :
    ∃ t w k : ℤ, Algebra.norm ℤ β = t ^ 2 + w ∧ k ^ 2 = 4 * n * w := by
  obtain ⟨t, ht⟩ := even_two_re hn β
  obtain ⟨k, hk⟩ := exists_two_re (β * sqrtNeg n)
  have hN := normZ_eq_re_im β
  have hre : ((β * sqrtNeg n : 𝓞 (QNeg n)) : QNeg n).re = -(n : ℚ) * (β : QNeg n).im := by
    simp [RingOfIntegers.coe_eq_algebraMap, coe_sqrtNeg]
  rw [hre] at hk
  have hret : (β : QNeg n).re = t := by linarith
  refine ⟨t, Algebra.norm ℤ β - t ^ 2, k, by ring, ?_⟩
  have : (k : ℚ) ^ 2 = 4 * n * ((Algebra.norm ℤ β : ℚ) - (t : ℚ) ^ 2) := by
    rw [← hk, hN, hret]; ring
  exact_mod_cast this

theorem norm_mod_four (hn : n % 4 = 1) (β : 𝓞 (QNeg n)) (hodd : Algebra.norm ℤ β % 2 = 1) :
    Algebra.norm ℤ β % 4 = 1 := by
  obtain ⟨t, w, k, hN, hk⟩ := norm_eq_sq_add hn β
  have h4 := congrArg (fun x : ℤ => (x : ZMod 4)) hk
  push_cast at h4
  have hn4 : ((n : ℕ) : ZMod 4) = 1 := by rw [← ZMod.natCast_mod, hn]; rfl
  rw [hn4] at h4
  have hN4 := congrArg (fun x : ℤ => (x : ZMod 4)) hN
  push_cast at hN4
  -- `k² = 4w = 0` in `ZMod 4` forces `k` even; then `w ≡ (k/2)²`
  have hke : (2 : ℤ) ∣ k := by
    have key : ∀ x : ZMod 4, x ^ 2 = 4 * 1 * 0 + 0 → x = 0 ∨ x = 2 := by decide
    have hk0 : (k : ZMod 4) ^ 2 = 0 := by rw [h4]; ring_nf; rfl
    by_contra hk2
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
    have := congrArg (fun x : ℤ => (x : ZMod 4)) (show (2 * j + 1) ^ 2 = 4 * (j ^ 2 + j) + 1 by ring)
    push_cast at this hk0
    rw [hk0] at this
    have e : (4 : ZMod 4) = 0 := rfl
    rw [e, zero_mul, zero_add] at this
    exact absurd this (by decide)
  obtain ⟨j, rfl⟩ := hke
  have hw : w = n * w - (n - 1) * w := by ring
  have hjw : j ^ 2 = n * w := by nlinarith [hk]
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (n : ℤ) = 4 * c + 1 := ⟨(n : ℤ) / 4, by omega⟩
  have hw' : w = j ^ 2 - 4 * c * w := by rw [hjw, hc]; ring
  rw [hw'] at hN
  have key : ∀ a b : ZMod 4, a ^ 2 + b ^ 2 ≠ 3 := by decide
  have h3 := congrArg (fun x : ℤ => (x : ZMod 4)) hN
  push_cast at h3
  have e : (4 : ZMod 4) = 0 := rfl
  rw [e, zero_mul, zero_mul, sub_zero] at h3
  rcases (show Algebra.norm ℤ β % 4 = 1 ∨ Algebra.norm ℤ β % 4 = 3 by omega) with h | h
  · exact h
  · exfalso
    have : ((Algebra.norm ℤ β : ℤ) : ZMod 4) = 3 := by
      rw [← ZMod.intCast_mod, Nat.cast_ofNat, h]; rfl
    rw [this] at h3
    exact key _ _ h3.symm

theorem norm_sq_mod_prime (hn : n % 4 = 1) (hsq : Squarefree n) {p : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (β : 𝓞 (QNeg n)) : ∃ t : ℤ, (p : ℤ) ∣ Algebra.norm ℤ β - t ^ 2 := by
  obtain ⟨t, w, k, hN, hk⟩ := norm_eq_sq_add hn β
  refine ⟨t, ?_⟩
  rw [hN, add_sub_cancel_left]
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  obtain ⟨n', hn'⟩ := hpn
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hpn' : ¬ (p : ℤ) ∣ n' := by
    intro h
    obtain ⟨m, rfl⟩ := Int.natCast_dvd_natCast.1 h
    have := hsq p ⟨m, by rw [hn']; ring⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.1 this)
  have hpk : (p : ℤ) ∣ k := by
    apply hpZ.dvd_of_dvd_pow (n := 2)
    rw [hk, hn']; push_cast
    exact ⟨4 * n' * w, by ring⟩
  obtain ⟨k', rfl⟩ := hpk
  have : (p : ℤ) * (k' ^ 2 * p) = (p : ℤ) * (4 * n' * w) := by
    rw [hn'] at hk; push_cast at hk; linear_combination hk
  have h2 : k' ^ 2 * p = 4 * n' * w := mul_left_cancel₀ hpZ.ne_zero this
  have h3 : (p : ℤ) ∣ 4 * n' * w := ⟨k' ^ 2, by rw [← h2]; ring⟩
  rcases hpZ.dvd_or_dvd h3 with h | h
  · rcases hpZ.dvd_or_dvd h with h | h
    · exfalso
      have : (p : ℤ) ∣ 2 ^ 2 := by norm_num; exact h
      have := hpZ.dvd_of_dvd_pow this
      have := Int.le_of_dvd (by norm_num) this
      have := hp.two_le
      omega
    · exact absurd h hpn'
  · exact h

theorem finite_le_primes (I : Ideal (𝓞 (QNeg n))) (hI : I ≠ ⊥) :
    {𝔭 : HeightOneSpectrum (𝓞 (QNeg n)) | I ≤ 𝔭.asIdeal}.Finite :=
  (Ideal.finite_factors (by simpa using hI)).subset fun 𝔭 h𝔭 => Ideal.dvd_iff_le.2 h𝔭

/-- **Genus theory, explicitly**: for squarefree `n ≡ 1 (mod 4)`, `K_n(√−1)` and `K_n(√p)` (`p ∣ n`
prime) lie in the Hilbert class field `H_n` (via Bauer: a principal prime `𝔭 = β𝓞_K ∤ 2n` has
`N𝔭 ≡ 1 (mod 4)` and `N𝔭 ≡ t² (mod p)`, so `−1` and `p` are squares mod `𝔭` by quadratic
reciprocity in Mathlib's finite-field form `FiniteField.isSquare_odd_prime_iff`). -/
theorem adjSqrt_le_hilbertField (hn : n % 4 = 1) (hsq : Squarefree n) (a : ℤ)
    (ha : a = -1 ∨ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ a = p) : adjSqrt (QNeg n) a ≤ hilbertField n := by
  rw [hilbertField_eq_ringSubfield]
  have hI : (conductorOrder (QNeg n) 1).conductor * Ideal.span {((2 * n : ℕ) : 𝓞 (QNeg n))} ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    refine ⟨(conductorOrder (QNeg n) 1).conductor_ne_bot, ?_⟩
    rw [Ideal.span_singleton_eq_bot]
    exact_mod_cast (show 2 * n ≠ 0 by omega)
  refine le_of_splitSet_diff_subset _ (finite_le_primes _ hI) ?_
  rintro 𝔭 ⟨h𝔭, hT⟩
  have hT1 : ¬ (conductorOrder (QNeg n) 1).conductor ≤ 𝔭.asIdeal :=
    fun h => hT (le_trans Ideal.mul_le_left h)
  have h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := fun h =>
    hT (le_trans Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h))
  have h2 : (2 : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := fun h => h2n (by
    push_cast; exact 𝔭.asIdeal.mul_mem_right _ h)
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
  have hodd := card_quot_odd 𝔭 h2
  have hnn := normZ_nonneg (n := n) β
  have hc : ((Algebra.norm ℤ β).natAbs : ℤ) = Algebra.norm ℤ β := Int.natAbs_of_nonneg hnn
  rw [hq] at hodd
  have hodd' : Algebra.norm ℤ β % 2 = 1 := by rw [← hc]; exact_mod_cast hodd
  have h4 := norm_mod_four hn β hodd'
  have hq4 : (Algebra.norm ℤ β).natAbs % 4 = 1 := by
    have : ((Algebra.norm ℤ β).natAbs : ℤ) % 4 = 1 := by rw [hc]; exact h4
    exact_mod_cast this
  have h2a : ((2 * a : ℤ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := by
    rcases ha with rfl | ⟨p, hp, hpn, rfl⟩
    · intro h; apply h2
      have : -((2 * (-1) : ℤ) : 𝓞 (QNeg n)) ∈ 𝔭.asIdeal := 𝔭.asIdeal.neg_mem h
      simpa using this
    · intro h; apply h2n
      obtain ⟨n', hn'⟩ := hpn
      have h' : (2 * (n : ℤ)) = 2 * p * n' := by rw [hn']; push_cast; ring
      have hcast : ((2 * n : ℕ) : 𝓞 (QNeg n)) =
          ((2 * (p : ℤ) : ℤ) : 𝓞 (QNeg n)) * (n' : 𝓞 (QNeg n)) := by
        have := congrArg (fun z : ℤ => (z : 𝓞 (QNeg n))) h'
        push_cast at this ⊢; exact this
      rw [hcast]
      exact 𝔭.asIdeal.mul_mem_right _ h
  rw [mem_splitSet_adjSqrt_iff 𝔭 h2a]
  letI := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
  letI := Fintype.ofFinite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal)
  have hchar : ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) ≠ 2 := fun hc => h2 (by
    have : ((2 : ℕ) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal) = 0 := by rw [← hc]; exact ringChar.Nat.cast_ringChar
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
    simpa using this)
  have hcard : Fintype.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) = (Algebra.norm ℤ β).natAbs := by
    rw [← Nat.card_eq_fintype_card, hq]
  rcases ha with rfl | ⟨p, hp, hpn, rfl⟩
  · rw [Int.cast_neg, Int.cast_one, FiniteField.isSquare_neg_one_iff, hcard]
    omega
  · haveI := Fact.mk hp
    have hp2 : p ≠ 2 := by rintro rfl; obtain ⟨m, hm⟩ := hpn; omega
    rw [Int.cast_natCast, FiniteField.isSquare_odd_prime_iff hchar hp2, hcard,
      ZMod.χ₄_nat_one_mod_four hq4]
    simp only [Int.cast_one, one_mul, Int.cast_natCast]
    obtain ⟨t, ht⟩ := norm_sq_mod_prime hn hsq hp hpn β
    have hqt : (((Algebra.norm ℤ β).natAbs : ℕ) : ZMod p) = (t : ZMod p) ^ 2 := by
      rw [← Int.cast_natCast, hc, ← sub_eq_zero, ← Int.cast_pow, ← Int.cast_sub,
        ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact ht
    rw [hqt]
    by_cases ht0 : (t : ZMod p) = 0
    · rw [ht0]; simp
    · rw [quadraticChar_sq_one' ht0]; decide

/-- **`L_n(i) ⊆ H'_n`** for squarefree `n ≡ 1 (mod 4)` (in fact `L_n(i) ⊆ H_n ⊆ H'_n`). -/
theorem Lni_le_Hprimebar (hn : n % 4 = 1) (hsq : Squarefree n) : Lni n ≤ Hprimebar n := by
  rw [Hprimebar_eq_map, Lni, IntermediateField.adjoin_le_iff]
  have hmem : ∀ a : ℤ, (a = -1 ∨ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ a = p) → ∀ x : Qbar,
      x ^ 2 = (a : Qbar) → x ∈ ((Hprime n).restrictScalars ℚ).map (embed n) := by
    intro a ha x hx
    have hs : embed n (sqrtK (QNeg n) a) ∈ ((Hprime n).restrictScalars ℚ).map (embed n) :=
      ⟨_, hilbertField_le_Hprime n (adjSqrt_le_hilbertField hn hsq a ha
        (IntermediateField.mem_adjoin_simple_self _ _)), rfl⟩
    have hs2 : (embed n (sqrtK (QNeg n) a)) ^ 2 = (a : Qbar) := by
      rw [← map_pow, sqrtK_sq, map_intCast]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hx.trans hs2.symm) with h | h
    · rw [h]; exact hs
    · rw [h]; exact neg_mem hs
  rintro x (hx | ⟨p, hp, hx⟩)
  · exact hmem (-1) (Or.inl rfl) x (by rw [hx]; simp)
  · exact hmem p (Or.inr ⟨p, Nat.prime_of_mem_primeFactors hp, Nat.dvd_of_mem_primeFactors hp, rfl⟩)
      x (by rw [hx]; simp)

/-- **`ℍ'_n = Π_{d₀ ∣ n, d₀ ≡ 5 (8)} H'_{d₀}`** for squarefree `n ≡ 5 (mod 8)`: the factor `L_n(i)` of
TYZ's definition (L1320) is already contained in `H'_n`. -/
theorem HHprime_eq_iSup (hn : n % 8 = 5) (hsq : Squarefree n) :
    HHprime n = ⨆ d₀ ∈ n.divisors.filter (fun d => d % 8 = 5), Hprimebar d₀ := by
  apply le_antisymm
  · refine sup_le ?_ le_rfl
    refine le_trans (Lni_le_Hprimebar (by omega) hsq) ?_
    have hmem : n ∈ n.divisors.filter (fun d => d % 8 = 5) := by
      simp [Nat.mem_divisors, hn, NeZero.ne n]
    exact le_iSup₂ (f := fun d _ => Hprimebar d) n hmem
  · exact le_sup_right

end GenusFieldExplicit

end ZInQ.Contrib.TYZGenus.RingClass
