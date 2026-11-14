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

/-- A prime `𝔭` of `𝓞_{K_d}` containing an odd prime `p` with `(−d/p) = −1` is `p𝓞_{K_d}`. -/
theorem prime_eq_span_of_inert {p : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d)
    (hj : jacobiSym (-(d : ℤ)) p = -1) (𝔭 : Ideal (𝓞 (QNeg d))) [h𝔭 : 𝔭.IsPrime]
    (hp𝔭 : (p : 𝓞 (QNeg d)) ∈ 𝔭) : 𝔭 = Ideal.span {(p : 𝓞 (QNeg d))} := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hle : Ideal.span {(p : 𝓞 (QNeg d))} ≤ 𝔭 := (Ideal.span_singleton_le_iff_mem _).2 hp𝔭
  have hnormp : Ideal.absNorm (Ideal.span {(p : 𝓞 (QNeg d))}) = p ^ 2 := by
    rw [Ideal.absNorm_span_singleton]
    have e : (p : 𝓞 (QNeg d)) = algebraMap ℤ (𝓞 (QNeg d)) (p : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, RingOfIntegers.rank, QuadraticAlgebra.finrank_eq_two]
    simp
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

end StepC
end ZInQ.Contrib.TYZGenus.T318
