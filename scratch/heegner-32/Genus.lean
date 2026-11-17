import ZInQKernel.Contrib.OneProof.HeegnerPointRationalCd.Compose

/-!
# heegner-32: genus theory for `√d` in the ring class field of conductor `d`

* `adjSqrt_le_ringClassField`: `K(√d) ⊆ H_{𝒪_d}` for `K = ℚ(√−m)`, `d ≡ 1 (mod 4)` squarefree (Bauer's theorem, as the
  kernel's `adjSqrt_le_hilbertField`: a principal prime `β𝒪_K`, `β ∈ 𝒪_d`, has norm `≡ n² (mod d)`, so `d` is a square
  modulo it by quadratic reciprocity);
* `artin_sqrt`: the Artin symbol of a prime `𝔭` of degree one, `p ∤ 2d`, acts on `√d` by `(d/p)` (Euler's criterion).
-/

noncomputable section

set_option maxRecDepth 20000

open UpperHalfPlane Complex
open NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory IsDedekindDomain
  TauCeti.GlobalNumberFields.NumberFieldOrder

namespace ZInQ.Heegner32

open ZInQ.Contrib.TYZGenus.RingClass ZInQ.RouteK.Rank5b ZInQ.RouteK.Redei

/-! ## §1. The quadratic character of a finite field at an odd integer -/

theorem quadraticChar_natCast_eq_jacobi {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) :
    ∀ n : ℕ, Odd n → Nat.Coprime n (ringChar F) →
      quadraticChar F (n : F) = jacobiSym (ZMod.χ₄ (Fintype.card F) * Fintype.card F) n := by
  intro n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd h (by decide)
  | one => intro _ _; simp
  | prime p hp =>
    intro hodd hcop
    have := Fact.mk hp
    have hp2 : p ≠ 2 := by rintro rfl; exact absurd hodd (by decide)
    have hpc : ringChar F ≠ p := by
      intro h
      rw [← h] at hcop
      have := (Nat.coprime_self _).1 hcop
      have h2 := CharP.char_is_prime_or_zero F (ringChar F)
      rcases h2 with h2 | h2
      · exact h2.one_lt.ne' this
      · rw [h2] at h; exact hp.ne_zero h.symm
    rw [quadraticChar_odd_prime hF hp2 hpc, ← jacobiSym.legendreSym.to_jacobiSym]
    unfold legendreSym; push_cast; rfl
  | mul a b ha hb =>
    intro hodd hcop
    have hoa : Odd a := (Nat.odd_mul.1 hodd).1
    have hob : Odd b := (Nat.odd_mul.1 hodd).2
    have : NeZero a := ⟨hoa.pos.ne'⟩
    have : NeZero b := ⟨hob.pos.ne'⟩
    rw [Nat.cast_mul, map_mul, ha hoa (Nat.Coprime.coprime_mul_right hcop),
      hb hob (Nat.Coprime.coprime_mul_left hcop), jacobiSym.mul_right]

/-! ## §2. Norms of elements of `𝒪_d` are squares modulo `d` -/

section NormMod

variable {m : ℕ} [NeZero m]

open ZInQ.GZHeegner (exists_coords_theta coe_thetaO)

theorem norm_mod_d (hsq : Squarefree m) (h3 : m % 4 = 3) {d : ℕ} [NeZero d] (β : 𝓞 (QNeg m))
    (hβ : β ∈ (conductorOrder (QNeg m) d).toRingOfIntegers) :
    ∃ u : ℤ, (d : ℤ) ∣ Algebra.norm ℤ β - u ^ 2 := by
  rw [mem_toRingOfIntegers] at hβ
  obtain ⟨n, y, hy⟩ := hβ
  obtain ⟨z₀, z₁, rfl⟩ := exists_coords_theta hsq h3 y
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m = 4 * k + 3 := ⟨m / 4, by omega⟩
  have hN := normZ_eq_re_im β
  have hre : (β : QNeg m).re = n + d * (z₀ + z₁ / 2) := by
    rw [hy]
    simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast]
    rw [← RingOfIntegers.coe_eq_algebraMap, coe_thetaO]
    simp [div_eq_mul_inv]
  have him : (β : QNeg m).im = d * (z₁ / 2) := by
    rw [hy]
    simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast]
    rw [← RingOfIntegers.coe_eq_algebraMap, coe_thetaO]
    simp [div_eq_mul_inv]
  refine ⟨n + d * z₀, (n + d * z₀) * z₁ + d * z₁ ^ 2 * (k + 1), ?_⟩
  have hmQ : (m : ℚ) = 4 * k + 3 := by exact_mod_cast hk
  have : ((Algebra.norm ℤ β : ℤ) : ℚ) - ((n + d * z₀ : ℤ) : ℚ) ^ 2 =
      (d : ℚ) * (((n + d * z₀) * z₁ + d * z₁ ^ 2 * (k + 1) : ℤ) : ℚ) := by
    rw [hN, hre, him, hmQ]; push_cast; ring
  exact_mod_cast this

end NormMod

/-! ## §3. `K(√d)` lies in the ring class field of conductor `d` -/

section GenusField

variable {m : ℕ} [NeZero m]

/-- **Genus theory: `K(√d) ⊆ H_{𝒪_d}`** for `K = ℚ(√−m)` (`m ≡ 3 mod 4` squarefree) and `d ≡ 1 (mod 4)` squarefree
(Bauer's theorem; a prime `𝔭 = β𝒪_K ∤ 2d` with `β ∈ 𝒪_d` has `N𝔭 ≡ u² (mod d)`, so `d` is a square modulo `𝔭`). -/
theorem adjSqrt_le_ringClassField (hsq : Squarefree m) (h3 : m % 4 = 3) {d : ℕ} [NeZero d]
    (hd4 : d % 4 = 1) :
    adjSqrt (QNeg m) (d : ℤ) ≤ ringClassField (conductorOrder (QNeg m) d) := by
  rw [ringClassField_eq_ringSubfield]
  have hI : (conductorOrder (QNeg m) d).conductor * Ideal.span {((2 * d : ℕ) : 𝓞 (QNeg m))} ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    refine ⟨(conductorOrder (QNeg m) d).conductor_ne_bot, ?_⟩
    rw [Ideal.span_singleton_eq_bot]
    exact_mod_cast (show 2 * d ≠ 0 by omega)
  refine le_of_splitSet_diff_subset _ (finite_le_primes _ hI) ?_
  rintro 𝔭 ⟨h𝔭, hT⟩
  have hT1 : ¬ (conductorOrder (QNeg m) d).conductor ≤ 𝔭.asIdeal :=
    fun h => hT (le_trans Ideal.mul_le_left h)
  have h2d : ((2 * d : ℕ) : 𝓞 (QNeg m)) ∉ 𝔭.asIdeal := fun h =>
    hT (le_trans Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h))
  have h2 : (2 : 𝓞 (QNeg m)) ∉ 𝔭.asIdeal := fun h => h2d (by
    push_cast; exact 𝔭.asIdeal.mul_mem_right _ h)
  have hdP : (d : 𝓞 (QNeg m)) ∉ 𝔭.asIdeal := fun h => h2d (by
    push_cast; exact 𝔭.asIdeal.mul_mem_left _ h)
  have hJ := mem_primeTo_of_not_le 𝔭 hT1
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (conductorOrder (QNeg m) d).conductorModulus) :
    Ideal (𝓞 (QNeg m))).IsMaximal := 𝔭.isMaximal
  have h1 := (mem_splitSet_iff (conductorOrder (QNeg m) d) ⊥ ⟨_, hJ⟩ 𝔭 rfl).1 h𝔭
  rw [Subgroup.mem_bot, picClass_eq_one_iff] at h1
  obtain ⟨β, hβO, hspan⟩ := h1
  have hq : Nat.card (𝓞 (QNeg m) ⧸ 𝔭.asIdeal) = (Algebra.norm ℤ β).natAbs := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    change Ideal.absNorm (((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo
      (conductorOrder (QNeg m) d).conductorModulus) : Ideal (𝓞 (QNeg m)))) = _
    rw [hspan, Ideal.absNorm_span_singleton]
  have hnn := normZ_nonneg (n := m) β
  have hc : ((Algebra.norm ℤ β).natAbs : ℤ) = Algebra.norm ℤ β := Int.natAbs_of_nonneg hnn
  obtain ⟨u, hu⟩ := norm_mod_d hsq h3 β hβO
  have h2a : ((2 * (d : ℤ) : ℤ) : 𝓞 (QNeg m)) ∉ 𝔭.asIdeal := by
    intro h; apply h2d; push_cast at h ⊢; exact h
  rw [mem_splitSet_adjSqrt_iff 𝔭 h2a]
  letI := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 (QNeg m) ⧸ 𝔭.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
  letI := Fintype.ofFinite (𝓞 (QNeg m) ⧸ 𝔭.asIdeal)
  classical
  have hchar : ringChar (𝓞 (QNeg m) ⧸ 𝔭.asIdeal) ≠ 2 := fun hc => h2 (by
    have : ((2 : ℕ) : (𝓞 (QNeg m) ⧸ 𝔭.asIdeal)) = 0 := by rw [← hc]; exact ringChar.Nat.cast_ringChar
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
    simpa using this)
  have hcard : Fintype.card (𝓞 (QNeg m) ⧸ 𝔭.asIdeal) = (Algebra.norm ℤ β).natAbs := by
    rw [← Nat.card_eq_fintype_card, hq]
  have hd0F : ((d : ℕ) : (𝓞 (QNeg m) ⧸ 𝔭.asIdeal)) ≠ 0 := by
    intro h0; apply hdP
    rw [← Ideal.Quotient.eq_zero_iff_mem]; simpa using h0
  have hpF : (ringChar (𝓞 (QNeg m) ⧸ 𝔭.asIdeal)).Prime := CharP.char_is_prime (𝓞 (QNeg m) ⧸ 𝔭.asIdeal) (ringChar (𝓞 (QNeg m) ⧸ 𝔭.asIdeal))
  have hcop : Nat.Coprime d (ringChar (𝓞 (QNeg m) ⧸ 𝔭.asIdeal)) := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpF]
    intro hdvd
    exact hd0F ((ringChar.spec (𝓞 (QNeg m) ⧸ 𝔭.asIdeal) d).2 hdvd)
  have hdodd : Odd d := Nat.odd_iff.mpr (by omega)
  have hqc : quadraticChar (𝓞 (QNeg m) ⧸ 𝔭.asIdeal) ((d : ℕ) : (𝓞 (QNeg m) ⧸ 𝔭.asIdeal)) = 1 := by
    rw [quadraticChar_natCast_eq_jacobi hchar d hdodd hcop, jacobiSym.mul_left]
    -- `(χ₄ q / d) = 1` since `d ≡ 1 (mod 4)`
    have hχ : jacobiSym (ZMod.χ₄ (Fintype.card (𝓞 (QNeg m) ⧸ 𝔭.asIdeal)) : ℤ) d = 1 := by
      have hodd : Fintype.card (𝓞 (QNeg m) ⧸ 𝔭.asIdeal) % 2 = 1 := by
        rw [hcard, ← hq]; exact card_quot_odd 𝔭 h2
      rw [ZMod.χ₄_nat_eq_if_mod_four]
      split_ifs with h0 h1
      · omega
      · exact jacobiSym.one_left d
      · rw [jacobiSym.at_neg_one hdodd, ZMod.χ₄_nat_one_mod_four hd4]
    -- `(q / d) = (u² / d) = 1`
    have hqd : jacobiSym (Fintype.card (𝓞 (QNeg m) ⧸ 𝔭.asIdeal) : ℤ) d = 1 := by
      rw [hcard, hc]
      have hmod : Algebra.norm ℤ β % (d : ℤ) = u ^ 2 % (d : ℤ) :=
        (Int.ModEq.symm (Int.modEq_iff_dvd.2 hu)).eq
      rw [jacobiSym.mod_left' hmod]
      · apply jacobiSym.sq_one'
        rw [← Int.isCoprime_iff_gcd_eq_one]
        apply isCoprime_of_primes
        intro p hp hpu hpd
        apply hd0F
        have hpN : (p : ℤ) ∣ Algebra.norm ℤ β := by
          have : Algebra.norm ℤ β = (Algebra.norm ℤ β - u ^ 2) + u ^ 2 := by ring
          rw [this]; exact dvd_add (hpd.trans hu) (dvd_pow hpu two_ne_zero)
        -- `p ∣ N 𝔭 = card (𝓞 (QNeg m) ⧸ 𝔭.asIdeal)` forces `p = char (𝓞 (QNeg m) ⧸ 𝔭.asIdeal)`, which does not divide `d`
        have hpq : p ∣ Fintype.card (𝓞 (QNeg m) ⧸ 𝔭.asIdeal) := by
          rw [hcard]; exact Int.natCast_dvd_natCast.1 (by rw [hc]; exact hpN)
        obtain ⟨n', hn'⟩ := FiniteField.card (𝓞 (QNeg m) ⧸ 𝔭.asIdeal) (ringChar (𝓞 (QNeg m) ⧸ 𝔭.asIdeal))
        have hpc : p = ringChar (𝓞 (QNeg m) ⧸ 𝔭.asIdeal) := by
          rw [hn'.2] at hpq
          exact (Nat.prime_dvd_prime_iff_eq hp hpF).1 (hp.dvd_of_dvd_pow hpq)
        exact (ringChar.spec (𝓞 (QNeg m) ⧸ 𝔭.asIdeal) d).2 (by rw [← hpc]; exact Int.natCast_dvd_natCast.1 hpd)
    rw [hχ, hqd, mul_one]
  have hsqd : IsSquare ((d : ℕ) : (𝓞 (QNeg m) ⧸ 𝔭.asIdeal)) := (quadraticChar_one_iff_isSquare hd0F).1 hqc
  simpa using hsqd

end GenusField

/-! ## §4. The Artin symbol of a prime of degree one on `√d`, and `GenusSqrtD` -/

section Artin

variable {m : ℕ} [NeZero m]

/-- `√d` as an element of the ring class field of conductor `d`. -/
def sqrtH (hsq : Squarefree m) (h3 : m % 4 = 3) (d : ℕ) [NeZero d] (hd4 : d % 4 = 1) :
    ringClassField (conductorOrder (QNeg m) d) :=
  ⟨sqrtK (QNeg m) (d : ℤ), adjSqrt_le_ringClassField hsq h3 hd4
    (IntermediateField.mem_adjoin_simple_self _ _)⟩

theorem sqrtH_sq (hsq : Squarefree m) (h3 : m % 4 = 3) (d : ℕ) [NeZero d] (hd4 : d % 4 = 1) :
    sqrtH hsq h3 d hd4 ^ 2 = (d : ringClassField (conductorOrder (QNeg m) d)) := by
  apply Subtype.ext
  show sqrtK (QNeg m) (d : ℤ) ^ 2 = _
  rw [sqrtK_sq]; simp

/-- `√d` in `𝓞` of the ring class field. -/
def sqrtHO (hsq : Squarefree m) (h3 : m % 4 = 3) (d : ℕ) [NeZero d] (hd4 : d % 4 = 1) :
    𝓞 (ringClassField (conductorOrder (QNeg m) d)) :=
  ⟨sqrtH hsq h3 d hd4, by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (d : ℤ), Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sqrtH_sq, eq_intCast]
    push_cast; ring⟩

theorem sqrtHO_sq (hsq : Squarefree m) (h3 : m % 4 = 3) (d : ℕ) [NeZero d] (hd4 : d % 4 = 1) :
    sqrtHO hsq h3 d hd4 ^ 2 = (d : 𝓞 (ringClassField (conductorOrder (QNeg m) d))) := by
  apply RingOfIntegers.ext
  simp only [RingOfIntegers.coe_eq_algebraMap, map_pow, map_natCast]
  exact sqrtH_sq hsq h3 d hd4

set_option maxHeartbeats 2000000 in
/-- **The Artin symbol of a prime `𝔭` of degree one, `N𝔭 = p ∤ 2d`, acts on `√d` by `(p/d)`** (Euler's criterion
`d^{(p−1)/2} ≡ (d/p)` and quadratic reciprocity for `d ≡ 1 mod 4`). -/
theorem artin_sqrtH (hsq : Squarefree m) (h3 : m % 4 = 3) {d : ℕ} [NeZero d] (hd4 : d % 4 = 1)
    (J : integralIdealsPrimeTo (conductorOrder (QNeg m) d).conductorModulus)
    [(J : Ideal (𝓞 (QNeg m))).IsMaximal] {p : ℕ} (hp : p.Prime)
    (hN : Ideal.absNorm (J : Ideal (𝓞 (QNeg m))) = p) (hp2d : ¬ (p : ℤ) ∣ 2 * d) :
    ringClassArtinEquiv (conductorOrder (QNeg m) d) ((conductorOrder (QNeg m) d).picClass J)
      (sqrtH hsq h3 d hd4) =
      ((jacobiSym p d : ℤ) : ringClassField (conductorOrder (QNeg m) d)) * sqrtH hsq h3 d hd4 := by
  obtain ⟨Q, hQp, hQo⟩ := (inferInstance : Nonempty ((J : Ideal (𝓞 (QNeg m))).primesOver (𝓞 (ringClassField (conductorOrder (QNeg m) d)))))
  have hF := isArithFrobAt_ringClassArtinEquiv_picClass (conductorOrder (QNeg m) d) J Q
  set s := sqrtHO hsq h3 d hd4
  have hq : Nat.card (𝓞 (QNeg m) ⧸ Q.under (𝓞 (QNeg m))) = p := by
    rw [← Ideal.over_def Q (J : Ideal (𝓞 (QNeg m))), ← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h := hF s
  simp only [MulSemiringAction.toAlgHom_apply] at h
  rw [hq] at h
  have hp2 : p ≠ 2 := by rintro rfl; exact hp2d ⟨d, rfl⟩
  have hodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).2 hp2
  have hpd : ¬ (p : ℤ) ∣ d := fun h' => hp2d (dvd_mul_of_dvd_right h' _)
  have := Fact.mk hp
  set L := legendreSym p d with hL
  -- `p ∈ Q`
  have hpQ : (p : 𝓞 (ringClassField (conductorOrder (QNeg m) d))) ∈ Q := by
    have hpJ : ((p : ℕ) : 𝓞 (QNeg m)) ∈ (J : Ideal (𝓞 (QNeg m))) := by
      rw [← hN]; exact Ideal.absNorm_mem _
    have := (Ideal.mem_of_liesOver Q (J : Ideal (𝓞 (QNeg m))) _).1 hpJ
    simpa using this
  -- Euler: `d^{(p-1)/2} ≡ L (mod p)`
  have heuler : ((d : ℤ) ^ (p / 2) - L : ℤ) ∈ Ideal.span {(p : ℤ)} := by
    rw [Ideal.mem_span_singleton, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hL, legendreSym.eq_pow]; simp
  have heQ : (((d : ℤ) ^ (p / 2) - L : ℤ) : 𝓞 (ringClassField (conductorOrder (QNeg m) d))) ∈ Q := by
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.1 heuler
    rw [ht]; push_cast; exact Q.mul_mem_right _ hpQ
  have hpow : s ^ p = s * (d : 𝓞 (ringClassField (conductorOrder (QNeg m) d))) ^ (p / 2) := by
    have hp' : p = 2 * (p / 2) + 1 := by omega
    conv_lhs => rw [hp', pow_succ, pow_mul, sqrtHO_sq]
    ring
  have hsL : ringClassArtinEquiv (conductorOrder (QNeg m) d) ((conductorOrder (QNeg m) d).picClass J) • s - (L : 𝓞 (ringClassField (conductorOrder (QNeg m) d))) * s ∈ Q := by
    have : ringClassArtinEquiv (conductorOrder (QNeg m) d) ((conductorOrder (QNeg m) d).picClass J) • s - (L : 𝓞 (ringClassField (conductorOrder (QNeg m) d))) * s = (ringClassArtinEquiv (conductorOrder (QNeg m) d) ((conductorOrder (QNeg m) d).picClass J) • s - s ^ p) + s * ((((d : ℤ) ^ (p / 2) - L : ℤ) : 𝓞 (ringClassField (conductorOrder (QNeg m) d)))) := by
      rw [hpow]; push_cast; ring
    rw [this]; exact Q.add_mem h (Q.mul_mem_left _ heQ)
  have hsq2 : (ringClassArtinEquiv (conductorOrder (QNeg m) d) ((conductorOrder (QNeg m) d).picClass J) • s) ^ 2 = s ^ 2 := by
    rw [← smul_pow', sqrtHO_sq]
    exact map_natCast (MulSemiringAction.toRingHom _ (𝓞 (ringClassField (conductorOrder (QNeg m) d))) (ringClassArtinEquiv (conductorOrder (QNeg m) d) ((conductorOrder (QNeg m) d).picClass J))) d
  have hL1 : L = 1 ∨ L = -1 := by
    have h0 : L ≠ 0 := by
      rw [hL, Ne, legendreSym.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpd
    rcases legendreSym.eq_one_or_neg_one p (a := d) (by
      rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have hAs : ringClassArtinEquiv (conductorOrder (QNeg m) d) ((conductorOrder (QNeg m) d).picClass J) • s = (L : 𝓞 (ringClassField (conductorOrder (QNeg m) d))) * s := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq2 with h4 | h4 <;> rcases hL1 with hL' | hL'
    · rw [h4, hL']; simp
    · exfalso
      rw [h4, hL'] at hsL
      have h2s : 2 * s ∈ Q := by
        have : 2 * s = s - ((-1 : ℤ) : 𝓞 (ringClassField (conductorOrder (QNeg m) d))) * s := by push_cast; ring
        rw [this]; exact hsL
      have h4d : ((4 * d : ℤ) : 𝓞 (ringClassField (conductorOrder (QNeg m) d))) ∈ Q := by
        have : ((4 * d : ℤ) : 𝓞 (ringClassField (conductorOrder (QNeg m) d))) = (2 * s) * (2 * s) := by
          have := sqrtHO_sq hsq h3 d hd4; push_cast; linear_combination (-4 : 𝓞 (ringClassField (conductorOrder (QNeg m) d))) * this
        rw [this]; exact Q.mul_mem_left _ h2s
      have h4dJ : ((4 * d : ℤ) : 𝓞 (QNeg m)) ∈ (J : Ideal (𝓞 (QNeg m))) := by
        rw [Ideal.mem_of_liesOver Q (J : Ideal (𝓞 (QNeg m))), map_intCast]; exact h4d
      obtain ⟨p', hp', hlies⟩ := exists_prime_liesOver (J : Ideal (𝓞 (QNeg m)))
        (by intro hb; rw [hb, Ideal.absNorm_bot] at hN; exact hp.ne_zero hN.symm)
      have hpp' : p' = p := by
        have h1 := natCast_mem_of_liesOver (p := p') (J : Ideal (𝓞 (QNeg m)))
        have h2 : ((p : ℕ) : 𝓞 (QNeg m)) ∈ (J : Ideal (𝓞 (QNeg m))) := by
          rw [← hN]; exact Ideal.absNorm_mem _
        have h3' := (intCast_mem_iff_of_liesOver (p := p') (J : Ideal (𝓞 (QNeg m))) p).1 (by simpa using h2)
        exact ((Nat.prime_dvd_prime_iff_eq hp' hp).1 (by exact_mod_cast h3'))
      subst hpp'
      have h4 := (intCast_mem_iff_of_liesOver (p := p') (J : Ideal (𝓞 (QNeg m))) (4 * d)).1 h4dJ
      apply hp2d
      have : (4 * (d : ℤ)) = 2 * (2 * d) := by ring
      rw [this] at h4
      rcases (Nat.prime_iff_prime_int.1 hp').dvd_or_dvd h4 with h5 | h5
      · exact dvd_mul_of_dvd_left h5 _
      · exact h5
    · exfalso
      rw [h4, hL'] at hsL
      have h2s : -(2 * s) ∈ Q := by
        have : -(2 * s) = -s - ((1 : ℤ) : 𝓞 (ringClassField (conductorOrder (QNeg m) d))) * s := by push_cast; ring
        rw [this]; exact hsL
      have h2s' : 2 * s ∈ Q := by simpa using Q.neg_mem h2s
      have h4d : ((4 * d : ℤ) : 𝓞 (ringClassField (conductorOrder (QNeg m) d))) ∈ Q := by
        have : ((4 * d : ℤ) : 𝓞 (ringClassField (conductorOrder (QNeg m) d))) = (2 * s) * (2 * s) := by
          have := sqrtHO_sq hsq h3 d hd4; push_cast; linear_combination (-4 : 𝓞 (ringClassField (conductorOrder (QNeg m) d))) * this
        rw [this]; exact Q.mul_mem_left _ h2s'
      have h4dJ : ((4 * d : ℤ) : 𝓞 (QNeg m)) ∈ (J : Ideal (𝓞 (QNeg m))) := by
        rw [Ideal.mem_of_liesOver Q (J : Ideal (𝓞 (QNeg m))), map_intCast]; exact h4d
      obtain ⟨p', hp', hlies⟩ := exists_prime_liesOver (J : Ideal (𝓞 (QNeg m)))
        (by intro hb; rw [hb, Ideal.absNorm_bot] at hN; exact hp.ne_zero hN.symm)
      have hpp' : p' = p := by
        have h2 : ((p : ℕ) : 𝓞 (QNeg m)) ∈ (J : Ideal (𝓞 (QNeg m))) := by
          rw [← hN]; exact Ideal.absNorm_mem _
        have h3' := (intCast_mem_iff_of_liesOver (p := p') (J : Ideal (𝓞 (QNeg m))) p).1 (by simpa using h2)
        exact ((Nat.prime_dvd_prime_iff_eq hp' hp).1 (by exact_mod_cast h3'))
      subst hpp'
      have h4 := (intCast_mem_iff_of_liesOver (p := p') (J : Ideal (𝓞 (QNeg m))) (4 * d)).1 h4dJ
      apply hp2d
      have : (4 * (d : ℤ)) = 2 * (2 * d) := by ring
      rw [this] at h4
      rcases (Nat.prime_iff_prime_int.1 hp').dvd_or_dvd h4 with h5 | h5
      · exact dvd_mul_of_dvd_left h5 _
      · exact h5
    · rw [h4, hL']; simp
  -- back to `H`, and `L = (p/d)`
  have hLJ : L = jacobiSym p d := by
    rw [hL, jacobiSym.legendreSym.to_jacobiSym]
    exact_mod_cast jacobiSym.quadratic_reciprocity_one_mod_four hd4 (Nat.odd_iff.2 hodd)
  have := congrArg (fun x : 𝓞 (ringClassField (conductorOrder (QNeg m) d)) => (x : ringClassField (conductorOrder (QNeg m) d))) hAs
  rw [← hLJ]
  first
    | exact_mod_cast this
    | (push_cast at this; exact this)
    | simpa [s, sqrtHO] using this

end Artin

/-! ## §5. `GenusSqrtD`, proved, and the main theorem -/

open ZInQ.Contrib.TYZGenus.CM (ιC)
open ZInQ.GZWeil (gaussD)

/-- **`GenusSqrtD`, proved.** -/
theorem genusSqrtD : GenusSqrtD := by
  intro m _ hmsq hm3 d _ hd4 hdsq e he σ J a ha hNJ hcop2d hcase hart
  set w := sqrtH hmsq hm3 d hd4 with hw
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hg2 := ZInQ.GZWeil.gaussD_sq hd4 hdsq
  have hz2 : (ιC (e (w : SeparableClosure (QNeg m)))) ^ 2 = (d : ℂ) := by
    rw [← map_pow, ← map_pow]
    have : ((w : SeparableClosure (QNeg m))) ^ 2 = (d : SeparableClosure (QNeg m)) := by
      have := congrArg (fun x : ringClassField (conductorOrder (QNeg m) d) =>
        (x : SeparableClosure (QNeg m))) (sqrtH_sq hmsq hm3 d hd4)
      simpa using this
    rw [this]; simp
  have hzg : ιC (e (w : SeparableClosure (QNeg m))) = gaussD d ∨
      ιC (e (w : SeparableClosure (QNeg m))) = -gaussD d := by
    apply sq_eq_sq_iff_eq_or_eq_neg.1; rw [hz2, hg2]
  -- `σ z = χ z` gives `σ g = χ g`
  have conclude : ∀ χ : ℤ, σ (ιC (e (w : SeparableClosure (QNeg m)))) =
      (χ : ℂ) * ιC (e (w : SeparableClosure (QNeg m))) → σ (gaussD d) = (χ : ℂ) * gaussD d := by
    intro χ h
    rcases hzg with hz | hz
    · rw [hz] at h; exact h
    · rw [hz, map_neg] at h; linear_combination -h
  rcases hcase with ⟨hJ1, rfl⟩ | ⟨hmax, hprime⟩
  · -- `J = 𝒪_K`: the Artin symbol is trivial
    have hJ : J = 1 := Subtype.ext (by rw [hJ1]; simp [Ideal.one_eq_top])
    apply conclude
    rw [hart w, hJ, map_one, map_one, AlgEquiv.one_apply, jacobiSym.one_left]; simp
  · set p := a.natAbs with hp
    have hap : a = p := by rw [hp]; exact (Int.natAbs_of_nonneg ha.le).symm
    have hp2d : ¬ (p : ℤ) ∣ 2 * d := by
      intro h
      rw [← hap] at h
      have := hcop2d.isUnit_of_dvd' (dvd_refl a) h
      rw [Int.isUnit_iff] at this
      have : p = 1 := by omega
      exact hprime.one_lt.ne' this
    have hA := artin_sqrtH hmsq hm3 hd4 J hprime hNJ hp2d
    apply conclude
    rw [hart w, hA, hap]
    first
      | (simp; exact Or.inl rfl)
      | (simp [hw])
      | (simp; rfl)

/-- **`GZStatements.GrossZagierHeegnerCd` (the `C_d` form of `hL3`) from the main theorem of CM and the two printed
Gross–Zagier statements alone.** Chebotarev at conductor `d` and genus theory are proved. -/
theorem grossZagierHeegnerCd_of_hCM (hCM : T5Glue.ShimuraMainCM)
    (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd) (hGC : ZInQ.GZHL3.GrossConjugationCd) :
    ZInQ.GZStatements.GrossZagierHeegnerCd :=
  grossZagierHeegnerCd_of_genus' hCM genusSqrtD hGZ hGC

/-- **The even-`c` Heegner point of `C_d` from the main theorem of CM alone.** -/
theorem heegnerPointRationalCdEven_of_hCM (hCM : T5Glue.ShimuraMainCM) : HeegnerPointRationalCdEven :=
  heegnerPointRationalCdEven_of_twist (twistTransportCd_of_genus hCM ringClassJd genusSqrtD)

end ZInQ.Heegner32
