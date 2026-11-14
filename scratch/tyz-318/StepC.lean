import ZInQKernel.Contrib.TYZGenus.RingClassBridge
open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.RingClass ZInQ.RouteK.Rank5b NumberField
open TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory
open IsDedekindDomain

namespace ZInQ.Contrib.TYZGenus.T318

section StepC
variable {d : ℕ} [NeZero d]

instance instFDHprime : FiniteDimensional (QNeg d) (Hprime d) := by
  rw [Hprime_eq_ringSubfield]; infer_instance
instance instGalHprime : IsGalois (QNeg d) (Hprime d) := by
  rw [Hprime_eq_ringSubfield]; infer_instance
instance instFDQHprime : FiniteDimensional ℚ (Hprime d) := Module.Finite.trans (QNeg d) (Hprime d)
instance instNFHprime : NumberField (Hprime d) := ⟨⟩

theorem absNorm_span_natCast (p : ℕ) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 (QNeg d))}) = p ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have e : (p : 𝓞 (QNeg d)) = algebraMap ℤ (𝓞 (QNeg d)) (p : ℤ) := by simp
  rw [e, Algebra.norm_algebraMap, RingOfIntegers.rank, QuadraticAlgebra.finrank_eq_two]
  simp

/-- A prime `𝔭` of `𝓞_{K_d}` containing an odd prime `p` with `(−d/p) = −1` is `p𝓞_{K_d}`. -/
theorem prime_eq_span_of_inert {p : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d)
    (hj : jacobiSym (-(d : ℤ)) p = -1) (𝔭 : Ideal (𝓞 (QNeg d))) [h𝔭 : 𝔭.IsPrime]
    (hp𝔭 : (p : 𝓞 (QNeg d)) ∈ 𝔭) : 𝔭 = Ideal.span {(p : 𝓞 (QNeg d))} := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hle : Ideal.span {(p : 𝓞 (QNeg d))} ≤ 𝔭 := (Ideal.span_singleton_le_iff_mem _).2 hp𝔭
  have hnormp : Ideal.absNorm (Ideal.span {(p : 𝓞 (QNeg d))}) = p ^ 2 := absNorm_span_natCast p
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hmul : Ideal.absNorm 𝔭 * Ideal.absNorm J = p ^ 2 := by
    rw [← map_mul, ← hJ, hnormp]
  have hdvd : Ideal.absNorm 𝔭 ∣ p ^ 2 := ⟨_, hmul.symm⟩
  rcases (Nat.dvd_prime_pow hp).1 hdvd with ⟨k, hk, hk'⟩
  interval_cases k
  · exact absurd (Ideal.absNorm_eq_one_iff.1 (by simpa using hk')) h𝔭.ne_top
  · exfalso
    rw [pow_one] at hk'
    have h𝔭ne : 𝔭 ≠ ⊥ := by
      intro h0; rw [h0, Ideal.mem_bot] at hp𝔭
      exact hp.ne_zero (by exact_mod_cast hp𝔭)
    haveI : 𝔭.IsMaximal := h𝔭.isMaximal h𝔭ne
    letI := Ideal.Quotient.field 𝔭
    have hcard : Nat.card (𝓞 (QNeg d) ⧸ 𝔭) = p := by
      rw [← hk', ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    haveI : Finite (𝓞 (QNeg d) ⧸ 𝔭) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
    haveI : CharP (𝓞 (QNeg d) ⧸ 𝔭) p := by
      rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast (Ideal.Quotient.mk 𝔭),
        Ideal.Quotient.eq_zero_iff_mem]
      exact hp𝔭
    let f : ZMod p →+* 𝓞 (QNeg d) ⧸ 𝔭 := ZMod.castHom (dvd_refl p) _
    have hinj : Function.Injective f := f.injective
    have hbij : Function.Bijective f := by
      refine (Function.Injective.bijective_of_nat_card_le hinj ?_)
      rw [hcard, Nat.card_zmod]
    obtain ⟨z, hz⟩ := hbij.2 (Ideal.Quotient.mk 𝔭 (sqrtNeg d))
    have hsq : z * z = ((-(d : ℤ) : ℤ) : ZMod p) := by
      apply hinj
      rw [map_mul, hz, ← map_mul, sqrtNeg_mul_self, map_intCast, map_neg, map_natCast]
      push_cast; rfl
    have ha0 : ((-(d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_neg]
      exact_mod_cast hpd
    have h1 : legendreSym p (-(d : ℤ)) = 1 := (legendreSym.eq_one_iff p ha0).2 ⟨z, hsq.symm⟩
    rw [jacobiSym.legendreSym.to_jacobiSym, hj] at h1
    norm_num at h1
  · have hJ1 : Ideal.absNorm J = 1 := by
      rw [hk'] at hmul
      have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
      nlinarith [hmul]
    rw [Ideal.absNorm_eq_one_iff] at hJ1
    rw [hJ, hJ1, Ideal.mul_top]

/-- **Step C (ring class field theory, proved)**: let `p` be an odd prime, `p ∤ d`, inert in `K_d`, and
`Q` a prime of `𝓞_{H'_d}` containing `p`. Then `𝓞/Q ⊆ F_{p²}` and the inertia group of `Q` in
`Gal(H'_d/K_d)` is trivial: `p𝓞_{K_d}` has trivial class in `Pic(ℤ + 4𝓞_{K_d})`, so it splits completely
in `H'_d` (ring-class's `mem_splitSet_iff`), and the fundamental identity
`#primes · #inertia · f = [H'_d : K_d]` forces `#inertia = f = 1`. -/
theorem hprime_inert_split (_hd : d % 8 = 5) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ d)
    (hj : jacobiSym (-(d : ℤ)) p = -1) (Q : Ideal (𝓞 (Hprime d))) [hQ : Q.IsPrime]
    (hpQ : (p : 𝓞 (Hprime d)) ∈ Q) :
    (∀ a : 𝓞 (Hprime d), a ^ (p ^ 2) - a ∈ Q) ∧
    (∀ τ : Gal(Hprime d / QNeg d), (∀ a : 𝓞 (Hprime d), τ • a - a ∈ Q) → τ = 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set 𝔭 : Ideal (𝓞 (QNeg d)) := Q.under (𝓞 (QNeg d)) with h𝔭def
  have hp𝔭 : (p : 𝓞 (QNeg d)) ∈ 𝔭 := by
    rw [h𝔭def, Ideal.under_def, Ideal.mem_comap, map_natCast]; exact hpQ
  have h𝔭eq : 𝔭 = Ideal.span {(p : 𝓞 (QNeg d))} := prime_eq_span_of_inert hp hpd hj 𝔭 hp𝔭
  have h𝔭ne : 𝔭 ≠ ⊥ := by
    intro h0; rw [h0, Ideal.mem_bot] at hp𝔭
    exact hp.ne_zero (by exact_mod_cast hp𝔭)
  haveI h𝔭max : 𝔭.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h𝔭ne
  -- `2 ∉ 𝔭`
  have h2 : (2 : 𝓞 (QNeg d)) ∉ 𝔭 := by
    intro h2
    have hco : IsCoprime (2 : ℤ) (p : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
      exact_mod_cast this
    obtain ⟨u, v, huv⟩ := hco
    have h1 : ((u * 2 + v * p : ℤ) : 𝓞 (QNeg d)) ∈ 𝔭 := by
      push_cast
      exact 𝔭.add_mem (𝔭.mul_mem_left _ h2) (𝔭.mul_mem_left _ hp𝔭)
    rw [huv, Int.cast_one] at h1
    exact h𝔭max.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  -- `𝔭` is prime to the conductor of `ℤ + 4𝓞_K`
  let 𝔭' : HeightOneSpectrum (𝓞 (QNeg d)) := ⟨𝔭, inferInstance, h𝔭ne⟩
  have hT : ¬ (O4 d).conductor ≤ 𝔭'.asIdeal := by
    intro hle
    have h4 : ((4 : ℕ) : 𝓞 (QNeg d)) * 1 ∈ 𝔭 := hle (natCast_mul_mem_conductor (QNeg d) 4 1)
    rw [mul_one, show ((4 : ℕ) : 𝓞 (QNeg d)) = 2 * 2 by norm_num] at h4
    exact h2 ((Ideal.IsPrime.mem_or_mem inferInstance h4).elim id id)
  have hJ := mem_primeTo_of_not_le 𝔭' hT
  haveI : ((⟨𝔭'.asIdeal, hJ⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
    Ideal (𝓞 (QNeg d))).IsMaximal := h𝔭max
  have hc : (O4 d).picClass ⟨𝔭'.asIdeal, hJ⟩ = 1 := by
    rw [picClass_eq_one_iff]
    exact ⟨(p : 𝓞 (QNeg d)), natCast_mem _ p, h𝔭eq⟩
  have hsplit : 𝔭' ∈ splitSet (QNeg d) (Hprime d) := by
    rw [Hprime_eq_ringSubfield]
    exact (mem_splitSet_iff (O4 d) _ ⟨_, hJ⟩ 𝔭' rfl).2 (hc ▸ Subgroup.one_mem _)
  have hsplit' : (𝔭.primesOver (𝓞 (Hprime d))).ncard = Module.finrank (QNeg d) (Hprime d) :=
    hsplit
  -- the fundamental identity
  have hfund := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank
    (G := Gal(Hprime d / QNeg d)) 𝔭 Q
  rw [hsplit', IsGalois.card_aut_eq_finrank, mul_assoc] at hfund
  have hpos : 0 < Module.finrank (QNeg d) (Hprime d) := Module.finrank_pos
  have h1 : Nat.card (Q.inertia Gal(Hprime d / QNeg d)) * Q.inertiaDeg (𝓞 (QNeg d)) = 1 := by
    have := hfund
    nth_rewrite 2 [← mul_one (Module.finrank (QNeg d) (Hprime d))] at this
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hI : Nat.card (Q.inertia Gal(Hprime d / QNeg d)) = 1 := Nat.eq_one_of_mul_eq_one_right h1
  have hf : Q.inertiaDeg (𝓞 (QNeg d)) = 1 := Nat.eq_one_of_mul_eq_one_left h1
  refine ⟨?_, ?_⟩
  · have hQne : Q ≠ ⊥ := by
      intro h0; rw [h0, Ideal.mem_bot] at hpQ
      exact hp.ne_zero (by exact_mod_cast hpQ)
    haveI hQmax : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQne
    have hcardQ : Nat.card (𝓞 (Hprime d) ⧸ Q) = p ^ 2 := by
      have h := Ideal.absNorm_pow_inertiaDeg 𝔭 Q
      rw [hf, pow_one, h𝔭eq, absNorm_span_natCast] at h
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, ← h]
    letI := Ideal.Quotient.field Q
    haveI : Finite (𝓞 (Hprime d) ⧸ Q) :=
      Nat.finite_of_card_ne_zero (by rw [hcardQ]; exact pow_ne_zero 2 hp.ne_zero)
    letI := Fintype.ofFinite (𝓞 (Hprime d) ⧸ Q)
    intro a
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero, ← hcardQ,
      Nat.card_eq_fintype_card, FiniteField.pow_card]
  · intro τ hτ
    have hmem : τ ∈ Q.inertia Gal(Hprime d / QNeg d) := hτ
    have hbot := Subgroup.eq_bot_of_card_eq _ hI
    rw [hbot] at hmem
    exact hmem

end StepC
end ZInQ.Contrib.TYZGenus.T318
