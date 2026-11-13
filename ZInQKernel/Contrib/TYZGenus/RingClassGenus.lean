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
* `exists_lift_picSquares`: a set `R ⊆ Pic(O)²` mapped bijectively onto `Cl(K)²`, `#R = #Cl(K)²`
  (for `O_{n,4}`: `#R = g(n)`, `exists_lift_picSquares_O4`) — candidates for TYZ's `Φ₀`.
* `ringClassFieldD_neg`: for squarefree `d ≡ 3 (mod 4)`, the ring class field of discriminant `−d`
  is the Hilbert class field `H_d` (the field of TYZ's class-7 CM points).
* `artinPrime`: the Artin isomorphism `Pic(O_{d,4})/⟨σ_{1+2ϖ}⟩ ≃* Gal(H'_d/K_d)` (TYZ's `Cl'_d`), the
  restriction of Tau Ceti's `ringClassArtinEquiv` (`artinPrime_mk_apply`).
* `artin4_sq_apply_of_sq`: squares of `Pic(O_{n,4})` fix every `√q ∈ H_{n,4}` (`q ∈ K_n`).
* `conjGal_artin4`: complex conjugation inverts the Artin symbols of `H_{d,4}`:
  `τ ∘ Art(c) ∘ τ⁻¹ = Art(c⁻¹)` (Chebotarev + transport of arithmetic Frobenius elements along `τ`).
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

section Lifts

variable {K : Type} [Field K] [NumberField K]

/-- **Lifts of `2Cl` into the squares of `Pic O`**: there is a set `R ⊆ Pic(O)²` mapped bijectively
onto `Cl(K)² = Pic(𝓞_K)²` by `Pic O → Cl(K)`; it has `#Cl(K)²` elements. (For `O = O_{n,4}` these are
the candidates for TYZ's `Φ₀` up to the factor `⟨σ_{1+2ϖ}⟩`; TYZ's exact choice is not recorded on this
host.) -/
theorem exists_lift_picSquares (O : NumberFieldOrder K) :
    ∃ R : Finset (Pic O), (∀ c ∈ R, c ∈ picSquares O) ∧
      Set.BijOn (picToMax O) (R : Set (Pic O)) (picSquares (maximalNumberFieldOrder K)) ∧
      R.card = Nat.card (picSquares (maximalNumberFieldOrder K)) := by
  classical
  have hlift : ∀ s : picSquares (maximalNumberFieldOrder K),
      ∃ c, c ∈ picSquares O ∧ picToMax O c = s := by
    rintro ⟨s, ⟨c, rfl⟩⟩
    obtain ⟨c', hc'⟩ := picToMax_surjective O c
    exact ⟨c' ^ 2, ⟨c', rfl⟩, by simp [hc']⟩
  choose f hf1 hf2 using hlift
  have hinj : Function.Injective f := fun s t h => Subtype.ext (by rw [← hf2 s, ← hf2 t, h])
  haveI : Fintype (picSquares (maximalNumberFieldOrder K)) := Fintype.ofFinite _
  refine ⟨Finset.univ.image f, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro c hc
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hc
    exact hf1 s
  · intro c hc
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hc)
    rw [hf2]; exact s.2
  · intro c hc c' hc' h
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hc)
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hc')
    rw [hf2, hf2] at h
    rw [Subtype.ext h]
  · intro s hs
    exact ⟨f ⟨s, hs⟩, Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ _)), hf2 _⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Nat.card_eq_fintype_card]

open ZInQ.RouteK.Rank5b in
/-- For TYZ's order `O_{n,4}`: such a lift has `g(n) = gCl n` elements. -/
theorem exists_lift_picSquares_O4 (n : ℕ) [NeZero n] :
    ∃ R : Finset (Pic (O4 n)), (∀ c ∈ R, c ∈ picSquares (O4 n)) ∧
      Set.BijOn (picToMax (O4 n)) (R : Set (Pic (O4 n)))
        (picSquares (maximalNumberFieldOrder (QNeg n))) ∧ R.card = gCl n := by
  obtain ⟨R, h1, h2, h3⟩ := exists_lift_picSquares (O4 n)
  exact ⟨R, h1, h2, by rw [h3, gCl_eq_card_picSquares]⟩

end Lifts

section ClassSeven

open ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZDecomp.CurveA

/-- **The ring class field of discriminant `−d`, `d ≡ 3 (mod 4)` squarefree, is the Hilbert class
field `H_d`** (TYZ's class-7 CM points have discriminant `−d`). -/
theorem ringClassFieldD_neg {d : ℕ} (hd : d % 4 = 3) (hsq : Squarefree d) :
    haveI : NeZero d := ⟨by omega⟩
    ringClassFieldD (-d) = ((hilbertField d).restrictScalars ℚ).map (embed d) := by
  haveI : NeZero d := ⟨by omega⟩
  have hab : (-(d : ℤ)).natAbs = d := by omega
  have hs : sqfPart d = d := by
    obtain ⟨b, hb, hs⟩ := sqfPart_spec d
    exact squarefree_eq_of_sq_mul_eq (e := 1) (by rw [hb]; ring) (by rw [hb]; omega) hs hsq
  have hc : condD (-d) = 1 := by
    rw [condD, hab, hs, if_pos hd, Nat.div_self (by omega)]
    rfl
  rw [ringClassFieldD, if_pos (by omega), hc, hab, hs, ringClassFieldBar_eq, conductorOrder_one]

end ClassSeven

section ArtinPrime

open ZInQ.RouteK.Rank5b

variable (d : ℕ) [NeZero d]

instance : (Subgroup.zpowers (artin4 d (sigmaClass d))).Normal := Subgroup.normal_of_comm _

/-- **The Artin isomorphism for `H'_d`**: `Pic(O_{d,4})/⟨σ_{1+2ϖ}⟩ ≃* Gal(H'_d/K_d)` (`Cl'_d` of TYZ). -/
def artinPrime : Pic (O4 d) ⧸ Subgroup.zpowers (sigmaClass d) ≃* Gal(Hprime d/QNeg d) :=
  (QuotientGroup.congr (Subgroup.zpowers (sigmaClass d)) (Subgroup.zpowers (artin4 d (sigmaClass d)))
      (artin4 d) (by rw [MonoidHom.map_zpowers]; rfl)).trans
    ((IsGalois.normalAutEquivQuotient (Subgroup.zpowers (artin4 d (sigmaClass d)))).trans
      (AlgEquiv.autCongr (IntermediateField.liftAlgEquiv _)))

/-- `artinPrime` is the restriction of the Artin symbol of `H_{d,4}`. -/
theorem artinPrime_mk_apply (c : Pic (O4 d)) (x : Hprime d) :
    ((artinPrime d (QuotientGroup.mk c) x : Hprime d) : SeparableClosure (QNeg d)) =
      ((artin4 d c ⟨x, Hprime_le_H4 d x.2⟩ : H4 d) : SeparableClosure (QNeg d)) := by
  have h := AlgEquiv.restrictNormal_commutes (artin4 d c)
    (IntermediateField.fixedField (Subgroup.zpowers (artin4 d (sigmaClass d))))
    ((IntermediateField.liftAlgEquiv
      (IntermediateField.fixedField (Subgroup.zpowers (artin4 d (sigmaClass d))))).symm ⟨x.1, x.2⟩)
  simp only [artinPrime, MulEquiv.trans_apply, QuotientGroup.congr_mk,
    IsGalois.normalAutEquivQuotient_apply, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    AlgEquiv.restrictNormalHom_apply]
  exact congrArg Subtype.val h

instance : FiniteDimensional (QNeg d) (Hprime d) := by
  rw [Hprime_eq_ringSubfield]; infer_instance

instance : IsGalois (QNeg d) (Hprime d) := by
  rw [Hprime_eq_ringSubfield]; infer_instance

theorem card_artinPrime : Nat.card (Pic (O4 d) ⧸ Subgroup.zpowers (sigmaClass d)) =
    Module.finrank (QNeg d) (Hprime d) := by
  rw [Nat.card_congr (artinPrime d).toEquiv, IsGalois.card_aut_eq_finrank]

end ArtinPrime

section SquaresFix

open ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZDecomp.CurveA

variable {n : ℕ} [NeZero n]

/-- **Squares of `Pic(O_{n,4})` fix every square root of an element of `K_n` lying in `H_{n,4}`**
(`Gal(K(√q)/K)` has exponent 2). With `adjI_le_H4`, `adjSqrt_two_le_H4` and
`adjSqrt_le_hilbertField`: `2Cl'_n` fixes `i`, `√2` and `√p` (`p ∣ n`), as TYZ use ("`t ∈ Φ₀ ⊂ 2Cl′_n`
fixes `i ∈ L_n`", `rv-tyz-inputs.md` §1.5). -/
theorem artin4_sq_apply_of_sq {x : SeparableClosure (QNeg n)} (hx : x ∈ H4 n)
    (hsq : ∃ q : QNeg n, x ^ 2 = algebraMap (QNeg n) _ q) (b : Pic (O4 n)) :
    ((artin4 n (b ^ 2) ⟨x, hx⟩ : H4 n) : SeparableClosure (QNeg n)) = x := by
  obtain ⟨q, hq⟩ := hsq
  set g := artin4 n b
  have hy : (⟨x, hx⟩ : H4 n) ^ 2 = algebraMap (QNeg n) (H4 n) q := Subtype.ext (by simpa using hq)
  have hg : g ⟨x, hx⟩ = ⟨x, hx⟩ ∨ g ⟨x, hx⟩ = -⟨x, hx⟩ := by
    have : g ⟨x, hx⟩ ^ 2 = (⟨x, hx⟩ : H4 n) ^ 2 := by rw [← map_pow, hy, AlgEquiv.commutes]
    exact sq_eq_sq_iff_eq_or_eq_neg.1 this
  rw [map_pow, pow_two, AlgEquiv.mul_apply]
  rcases hg with h | h
  · rw [h, h]
  · rw [h, map_neg, h, neg_neg]

end SquaresFix

section ConjInvertsArtin

open ZInQ.RouteK.Rank5b ZInQ.RouteK.Redei

variable {d : ℕ} [NeZero d] (τ : SeparableClosure (QNeg d) ≃ₐ[ℚ] SeparableClosure (QNeg d))

theorem mem_H4_of_mem (x : SeparableClosure (QNeg d)) (hx : x ∈ H4 d) : τ x ∈ H4 d := by
  have h := IntermediateField.normal_iff_forall_map_le'.1 (normal_H4 d) τ
  exact h ⟨x, hx, rfl⟩

/-- `τ` restricted to `H_{d,4}` (a ring automorphism; `τ` need not be `K`-linear). -/
def tauH : H4 d ≃+* H4 d where
  toFun x := ⟨τ x, mem_H4_of_mem τ x x.2⟩
  invFun x := ⟨τ.symm x, mem_H4_of_mem τ.symm x x.2⟩
  left_inv x := Subtype.ext (τ.symm_apply_apply _)
  right_inv x := Subtype.ext (τ.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul τ _ _)
  map_add' x y := Subtype.ext (map_add τ _ _)

@[simp] theorem coe_tauH (x : H4 d) : ((tauH τ x : H4 d) : SeparableClosure (QNeg d)) = τ x := rfl
@[simp] theorem coe_tauH_symm (x : H4 d) :
    (((tauH τ).symm x : H4 d) : SeparableClosure (QNeg d)) = τ.symm x := rfl

variable (σ : QNeg d ≃ₐ[ℚ] QNeg d)
  (hτ : ∀ k, τ (algebraMap (QNeg d) (SeparableClosure (QNeg d)) k) =
    algebraMap (QNeg d) (SeparableClosure (QNeg d)) (σ k))

include hτ in
theorem tauH_algebraMap (k : QNeg d) :
    tauH τ (algebraMap (QNeg d) (H4 d) k) = algebraMap (QNeg d) (H4 d) (σ k) :=
  Subtype.ext (hτ k)

include hτ in
theorem tauH_symm_algebraMap (k : QNeg d) :
    (tauH τ).symm (algebraMap (QNeg d) (H4 d) k) = algebraMap (QNeg d) (H4 d) (σ.symm k) := by
  apply (tauH τ).injective
  rw [RingEquiv.apply_symm_apply, tauH_algebraMap τ σ hτ, AlgEquiv.apply_symm_apply]

/-- `τ g τ⁻¹ ∈ Gal(H_{d,4}/K_d)` for `g ∈ Gal(H_{d,4}/K_d)`. -/
def conjGal (g : Gal(H4 d/QNeg d)) : Gal(H4 d/QNeg d) :=
  AlgEquiv.ofRingEquiv (f := (tauH τ).symm.trans (g.toRingEquiv.trans (tauH τ))) (fun k => by
    simp only [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv]
    rw [tauH_symm_algebraMap τ σ hτ, AlgEquiv.commutes, tauH_algebraMap τ σ hτ,
      AlgEquiv.apply_symm_apply])

theorem conjGal_apply (g : Gal(H4 d/QNeg d)) (x : H4 d) :
    conjGal τ σ hτ g x = tauH τ (g ((tauH τ).symm x)) := rfl

/-- `τ` on `𝓞_{H_{d,4}}`. -/
abbrev tauO : 𝓞 (H4 d) ≃+* 𝓞 (H4 d) := RingOfIntegers.mapRingEquiv (tauH τ)

include hτ in
theorem tauO_symm_algebraMap (x : 𝓞 (QNeg d)) :
    (tauO τ).symm (algebraMap (𝓞 (QNeg d)) (𝓞 (H4 d)) x) =
      algebraMap (𝓞 (QNeg d)) (𝓞 (H4 d)) ((cO σ).symm x) := by
  apply RingOfIntegers.ext
  simp only [RingOfIntegers.mapRingEquiv_symm_apply, RingOfIntegers.map_mk]
  rw [show ((algebraMap (𝓞 (QNeg d)) (𝓞 (H4 d)) x : 𝓞 (H4 d)) : H4 d) =
      algebraMap (QNeg d) (H4 d) (x : QNeg d) from rfl, tauH_symm_algebraMap τ σ hτ]
  rfl

theorem conjGal_smul (g : Gal(H4 d/QNeg d)) (y : 𝓞 (H4 d)) :
    conjGal τ σ hτ g • y = tauO τ (g • (tauO τ).symm y) := by
  apply RingOfIntegers.ext
  rfl

include hτ in
theorem under_comap_tauO (Q : Ideal (𝓞 (H4 d))) :
    (Q.comap (tauO τ).symm).under (𝓞 (QNeg d)) =
      (Q.under (𝓞 (QNeg d))).comap (cO σ).symm := by
  ext x
  simp only [Ideal.under_def, Ideal.mem_comap, RingHom.coe_coe]
  rw [tauO_symm_algebraMap τ σ hτ]

theorem card_quot_comap_equiv {R : Type*} [CommRing R] (I : Ideal R) (e : R ≃+* R) :
    Nat.card (R ⧸ I.comap e) = Nat.card (R ⧸ I) :=
  Nat.card_congr (Ideal.quotientEquiv _ I e
    (Ideal.map_comap_of_surjective _ e.surjective I).symm).toEquiv

include hτ in
/-- **`τ` transports arithmetic Frobenius elements**: if `g` is an arithmetic Frobenius at `Q`, then
`τ g τ⁻¹` is one at `τ(Q)`. -/
theorem isArithFrobAt_conjGal (g : Gal(H4 d/QNeg d)) (Q : Ideal (𝓞 (H4 d)))
    (hg : IsArithFrobAt (𝓞 (QNeg d)) g Q) :
    IsArithFrobAt (𝓞 (QNeg d)) (conjGal τ σ hτ g)
      (Q.comap (tauO τ).symm) := by
  intro y
  have hq : Nat.card (𝓞 (QNeg d) ⧸
      (Q.comap (tauO τ).symm).under (𝓞 (QNeg d))) =
      Nat.card (𝓞 (QNeg d) ⧸ Q.under (𝓞 (QNeg d))) := by
    rw [under_comap_tauO τ σ hτ, card_quot_comap_equiv]
  simp only [MulSemiringAction.toAlgHom_apply, Ideal.mem_comap, RingHom.coe_coe]
  rw [hq, map_sub, map_pow, conjGal_smul, RingEquiv.symm_apply_apply]
  have := hg ((tauO τ).symm y)
  simpa only [MulSemiringAction.toAlgHom_apply] using this

/-- The action of `σ` on the primes of `K_d`. -/
def conjPrime (𝔭 : HeightOneSpectrum (𝓞 (QNeg d))) : HeightOneSpectrum (𝓞 (QNeg d)) :=
  haveI : (𝔭.asIdeal.comap (cO σ).symm).IsMaximal :=
    Ideal.comap_isMaximal_of_equiv _
  ⟨𝔭.asIdeal.comap (cO σ).symm, inferInstance, by
    intro h
    rw [Ideal.comap_symm, Ideal.map_eq_bot_iff_of_injective (cO σ).injective] at h
    exact 𝔭.ne_bot h⟩

theorem conjPrime_injective : Function.Injective (conjPrime σ) := by
  intro 𝔭 𝔮 h
  apply HeightOneSpectrum.ext
  have := congrArg HeightOneSpectrum.asIdeal h
  exact Ideal.comap_injective_of_surjective _ (cO σ).symm.surjective this

set_option maxRecDepth 10000 in
include hτ in
/-- **Complex conjugation inverts the Artin symbols of `H_{d,4}`**: for `τ ∈ Aut(K_dˢ/ℚ)` acting on
`K_d` by the nontrivial automorphism, `τ ∘ Art(c) ∘ τ⁻¹ = Art(c⁻¹)` on `H_{d,4}` (TYZ: "`c` inverts
`Cl'_n`", `rv-tyz-inputs.md` §1.5; Cox, *Primes of the form x² + ny²*, Lemma 9.3). Proof:
Chebotarev gives a prime `𝔭` in the class of `c` with `σ(𝔭)` unramified; `τ` carries the Frobenius at
`Q | 𝔭` to a Frobenius at `τ(Q) | σ(𝔭)`, and `σ(𝔭)` has class `c⁻¹` (`picClass_conj`). -/
theorem conjGal_artin4 (hσ : σ ≠ 1) (c : Pic (O4 d)) :
    conjGal τ σ hτ (artin4 d c) = artin4 d c⁻¹ := by
  set T : Set (HeightOneSpectrum (𝓞 (QNeg d))) :=
    {𝔭 | (O4 d).conductor ≤ 𝔭.asIdeal} ∪
      conjPrime σ ⁻¹' (NumberField.Chebotarev.ramifiedPrimes (QNeg d) (H4 d) : Set (HeightOneSpectrum (𝓞 (QNeg d))))
  have hT : T.Finite := (finite_conductor_primes 4).union
    ((NumberField.Chebotarev.ramifiedPrimes (QNeg d) (H4 d)).finite_toSet.preimage (conjPrime_injective σ).injOn)
  have hD := NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet (QNeg d) (H4 d)
    (ConjClasses.mk (ringClassArtinEquiv (O4 d) c))
  have hδ : (Nat.card (ConjClasses.mk (ringClassArtinEquiv (O4 d) c)).carrier : ℝ) /
      Nat.card (H4 d ≃ₐ[QNeg d] H4 d) ≠ 0 := by
    apply div_ne_zero
    · have : Nonempty (ConjClasses.mk (ringClassArtinEquiv (O4 d) c)).carrier :=
        ⟨⟨_, ConjClasses.mem_carrier_mk⟩⟩
      exact_mod_cast (Nat.card_pos (α := (ConjClasses.mk
        (ringClassArtinEquiv (O4 d) c)).carrier)).ne'
    · exact_mod_cast (Nat.card_pos (α := H4 d ≃ₐ[QNeg d] H4 d)).ne'
  obtain ⟨𝔭, h𝔭, h𝔭T⟩ := ((hD.infinite hδ).sdiff hT).nonempty
  rw [Set.mem_union, not_or] at h𝔭T
  obtain ⟨hT1, hT2⟩ := h𝔭T
  have hJ := mem_primeTo_of_not_le 𝔭 hT1
  obtain ⟨⟨Q, hQp, hQo⟩, hF⟩ :=
    NumberField.Chebotarev.exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk h𝔭
  have hur := NumberField.Chebotarev.isUnramifiedAt_of_mem_frobeniusPrimeSet h𝔭 Q
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
    Ideal (𝓞 (QNeg d))).IsMaximal := 𝔭.isMaximal
  have : Q.LiesOver ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
    Ideal (𝓞 (QNeg d))) := hQo
  have hc : (O4 d).picClass ⟨_, hJ⟩ = c :=
    (ringClassArtinEquiv (O4 d)).injective (isArithFrobAt_eq_of_isUnramifiedAt
      (isArithFrobAt_ringClassArtinEquiv_picClass (O4 d) ⟨_, hJ⟩ Q) hF)
  -- the transported prime
  obtain ⟨Q', hQ'⟩ : ∃ Q' : Ideal (𝓞 (H4 d)), Q' = Q.comap (tauO τ).symm := ⟨_, rfl⟩
  have hJ' := conj_mem_primeTo σ hJ
  have : ((⟨_, hJ'⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
    Ideal (𝓞 (QNeg d))).IsMaximal := (conjPrime σ 𝔭).isMaximal
  have : Q'.IsPrime := hQ' ▸ Ideal.comap_isPrime _ _
  have hunder : Q'.under (𝓞 (QNeg d)) =
      𝔭.asIdeal.comap (cO σ).symm := by
    rw [hQ', under_comap_tauO τ σ hτ, ← Ideal.over_def Q 𝔭.asIdeal]
  have : Q'.LiesOver ((⟨_, hJ'⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
    Ideal (𝓞 (QNeg d))) := ⟨hunder.symm⟩
  have hur' : Algebra.IsUnramifiedAt (𝓞 (QNeg d)) Q' := by
    have h := hT2
    rw [Set.mem_preimage, Finset.mem_coe, NumberField.Chebotarev.mem_ramifiedPrimes_iff,
      not_not] at h
    have : Q'.LiesOver (conjPrime σ 𝔭).asIdeal := ⟨hunder.symm⟩
    exact h Q'
  have hF' := isArithFrobAt_ringClassArtinEquiv_picClass (O4 d) ⟨_, hJ'⟩ Q'
  have hG := isArithFrobAt_conjGal τ σ hτ (artin4 d c) Q hF
  rw [← hQ'] at hG
  rw [isArithFrobAt_eq_of_isUnramifiedAt hG hF', picClass_conj σ hσ ⟨_, hJ⟩, hc]

include hτ in
theorem conj_artin4_apply (hσ : σ ≠ 1) (c : Pic (O4 d)) (x : H4 d) :
    τ ((artin4 d c ((tauH τ).symm x) : H4 d) : SeparableClosure (QNeg d)) =
      ((artin4 d c⁻¹ x : H4 d) : SeparableClosure (QNeg d)) := by
  have := congrArg (fun g : Gal(H4 d/QNeg d) => ((g x : H4 d) : SeparableClosure (QNeg d)))
    (conjGal_artin4 τ σ hτ hσ c)
  simpa only [conjGal_apply, coe_tauH] using this

theorem exists_sigma_of_neg
    (h : τ (algebraMap (QNeg d) (SeparableClosure (QNeg d)) QuadraticAlgebra.omega) =
      -algebraMap (QNeg d) (SeparableClosure (QNeg d)) QuadraticAlgebra.omega) :
    ∃ σ : QNeg d ≃ₐ[ℚ] QNeg d, σ ≠ 1 ∧ ∀ k, τ (algebraMap (QNeg d) (SeparableClosure (QNeg d)) k) =
      algebraMap (QNeg d) (SeparableClosure (QNeg d)) (σ k) := by
  obtain ⟨σ, hσ⟩ := exists_conj_ne_one (n := d)
  refine ⟨σ, hσ, fun x => ?_⟩
  rw [algEquiv_algebraMap_eq τ x, h, algebraMap_eq_re_im (σ x), conj_apply σ hσ,
    QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  simp only [map_neg, zero_mul, add_zero]
  ring

end ConjInvertsArtin

end ZInQ.Contrib.TYZGenus.RingClass
