import ZInQKernel.Contrib.OneProof.RC.O7Character.Character
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Points

/-! The selected datum's quadratic character and the descended norm
character agree on the same conductor-one class. Tex 9180–9194. -/

noncomputable section

open NumberField IsDedekindDomain TauCeti.GlobalNumberFields
open TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open scoped NumberField nonZeroDivisors

namespace ZInQ.Manuscript.RC.O7Assemble

variable {F : Type} [Field F] [NumberField F] {d : ℤ}

theorem conductorOne_top : (conductorOrder F 1).conductor = ⊤ := by
  have h : conductorOrder F 1 = maximalNumberFieldOrder F := by
    ext x
    constructor
    · exact fun hx => conductorOrderSubalgebra_le_integralClosure F 1 hx
    · intro hx
      exact ⟨0, ⟨x, hx⟩, by simp; rfl⟩
  rw [h]
  exact conductor_maximal

private def integralClass (J : Ideal (𝓞 F)) (hJ : J ≠ 0) :
    integralIdealsPrimeTo (conductorOrder F 1).conductorModulus :=
  ⟨J, ((conductorOrder F 1).mem_integralIdealsPrimeTo_conductorModulus_iff).mpr
    ⟨hJ, by rw [conductorOne_top]; simp⟩⟩

/-- The prime-ideal specification of the datum character extends
multiplicatively to every integral ideal prime to the partner. -/
theorem chiSign_ideal {χ : Pic (conductorOrder F 1) →* ℂˣ}
    (hχ : IsQuadRingClassChar F 1 d χ)
    (J : integralIdealsPrimeTo (conductorOrder F 1).conductorModulus)
    (hJ : (Ideal.absNorm J.val).Coprime d.natAbs) :
    chiSign χ ((conductorOrder F 1).picClass J) = chiD d (Ideal.absNorm J.val) := by
  let S := conductorOrder F 1
  have hprime (v : HeightOneSpectrum (𝓞 F))
      (hv : (Ideal.absNorm v.asIdeal).Coprime d.natAbs) :
      chiSign χ (S.picClass (integralClass v.asIdeal v.ne_bot)) =
        chiD d (Ideal.absNorm v.asIdeal) := by
    have hd : (d : 𝓞 F) ∉ v.asIdeal := by
      intro h
      have hspan : Ideal.span {(d : 𝓞 F)} ≤ v.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr h
      have he : Ideal.absNorm (Ideal.span {(d : 𝓞 F)}) = d.natAbs ^ Module.finrank ℚ F := by
        rw [Ideal.absNorm_span_singleton]
        change (Algebra.norm ℤ (algebraMap ℤ (𝓞 F) d)).natAbs = _
        rw [Algebra.norm_algebraMap, Int.natAbs_pow, RingOfIntegers.rank]
      have hdiv := Ideal.absNorm_dvd_absNorm_of_le hspan
      rw [he] at hdiv
      have hh := hv.pow_right (Module.finrank ℚ F)
      exact (NumberField.HeightOneSpectrum.one_lt_absNorm v).ne'
        (Nat.dvd_one.mp (hh.gcd_eq_one ▸ Nat.dvd_gcd (dvd_refl _) hdiv))
    have h := hχ.2 v (integralClass v.asIdeal v.ne_bot).prop hd
    rw [← chiSign_coe hχ.1] at h
    exact_mod_cast h
  have aux (J₀ : Ideal (𝓞 F)) (hn : J₀ ≠ 0)
      (hc : (Ideal.absNorm J₀).Coprime d.natAbs) :
      chiSign χ (S.picClass (integralClass J₀ hn)) = chiD d (Ideal.absNorm J₀) := by
    induction J₀ using WfDvdMonoid.induction_on_irreducible with
    | zero => contradiction
    | unit U hU =>
      have he : U = 1 := by
        rw [Ideal.one_eq_top]
        exact top_unique (by simpa only [Ideal.one_eq_top] using Ideal.dvd_iff_le.mp hU.dvd)
      subst U
      change chiSign χ (S.picClass 1) = chiD d (Ideal.absNorm 1)
      simp [chiD, chiSign]
    | mul I P hI hP ih =>
      let v : HeightOneSpectrum (𝓞 F) :=
        ⟨P, Ideal.isPrime_of_prime (irreducible_iff_prime.mp hP), hP.ne_zero⟩
      have hc' : (Ideal.absNorm P * Ideal.absNorm I).Coprime d.natAbs := by
        simpa only [map_mul] using hc
      have hcop := Nat.coprime_mul_iff_left.mp hc'
      have hmul : integralClass (P * I) hn =
          integralClass P hP.ne_zero * integralClass I hI := rfl
      have hp := hprime v hcop.1
      change chiSign χ (S.picClass (integralClass P hP.ne_zero)) = _ at hp
      rw [hmul, map_mul, chiSign_mul hχ.1, ih hI hcop.2, hp, map_mul]
      simp only [chiD, Nat.cast_mul, jacobiSym.mul_left, v]
  exact aux J.val ((S.mem_integralIdealsPrimeTo_conductorModulus_iff.mp J.prop).1) hJ

/-- The selected datum and norm descent give the same sign on a common
conductor-one ideal label. -/
theorem chiSign_of_descent {χ : Pic (conductorOrder F 1) →* ℂˣ}
    (C : O7Actual.NormCharacterDescent F d) (hχ : IsQuadRingClassChar F 1 d χ)
    (J : integralIdealsPrimeTo (conductorOrder F 1).conductorModulus)
    (hJ : (Ideal.absNorm J.val).Coprime d.natAbs) :
    (C.choose ((conductorOrder F 1).picClass J) : ℤ) =
      chiSign χ ((conductorOrder F 1).picClass J) :=
  (C.choose_spec J hJ).trans (chiSign_ideal hχ J hJ).symm

end ZInQ.Manuscript.RC.O7Assemble
