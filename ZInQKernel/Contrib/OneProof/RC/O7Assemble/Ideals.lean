import ZInQKernel.Contrib.OneProof.RC.PicardFibers.TorusComparison
import ZInQKernel.Contrib.OneProof.RC.TorusWeights.Actual
import ZInQKernel.Contrib.TauCeti.RingTheory.ClassGroup.CoprimeRepresentative
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.ResidueDegree

/-! Integral representatives prime to the partner, with ideles normalized
at the ramified character primes (tex 9161–9166, 9191–9194). -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
open TauCeti.ClassFieldTheory
open ZInQ.Contrib.CloudB3RC53.CST
open scoped NumberField nonZeroDivisors RestrictedProduct

namespace ZInQ.Manuscript.RC.O7Assemble

open PicardFibers O7Actual O7Orbits Eichler

variable {F : Type} [Field F] [NumberField F]

theorem conductorOne : conductorOrder F 1 = maximalNumberFieldOrder F := by
  ext x
  constructor
  · exact fun hx => conductorOrderSubalgebra_le_integralClosure F 1 hx
  · intro hx
    exact ⟨0, ⟨x, hx⟩, by simp; rfl⟩

private def picOfMax {S : NumberFieldOrder F} (hs : S = maximalNumberFieldOrder F) :
    ClassGroup (𝓞 F) ≃* Pic S := by
  subst S
  exact MulEquiv.refl _

/-- Conductor one has the usual ideal class group of the ring of integers. -/
def picOne : ClassGroup (𝓞 F) ≃* Pic (conductorOrder F 1) :=
  picOfMax conductorOne

private def idealUnit {S : NumberFieldOrder F} (J : integralIdealsPrimeTo S.conductorModulus) :
    (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  FractionalIdeal.mk0 F ⟨J.val, mem_nonZeroDivisors_iff_ne_zero.mpr
    ((S.mem_integralIdealsPrimeTo_conductorModulus_iff.mp J.prop).1)⟩

theorem picClass_of_max {S : NumberFieldOrder F} (hs : S = maximalNumberFieldOrder F)
    (J : integralIdealsPrimeTo S.conductorModulus) :
    S.picClass J = picOfMax hs (ClassGroup.mk F (idealUnit J)) := by
  subst S
  rw [picClass_apply]
  let : IsFractionRing (maximalNumberFieldOrder F).toSubalgebra F :=
    inferInstanceAs (IsFractionRing (𝓞 F) F)
  change ClassGroup.mk F _ = ClassGroup.mk F (idealUnit J)
  congr 1
  apply Units.ext
  rw [coe_integralIdealsAwayConductorToInvertible_apply,
    coe_integralIdealsAwayConductorEquiv_symm_apply]
  let O := maximalNumberFieldOrder F
  let e := O.toRingOfIntegersEquiv
  have he : (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 F) = e.toRingHom := rfl
  rw [he]
  exact congrArg (fun I : Ideal (𝓞 F) => (I : FractionalIdeal (𝓞 F)⁰ F))
    (Ideal.map_comap_of_surjective e.toRingHom e.surjective J.val)

theorem exists_coprime_class (m : ℕ) (hm : m ≠ 0) (c : ClassGroup (𝓞 F)) :
    ∃ J : integralIdealsPrimeTo (conductorOrder F 1).conductorModulus,
      ClassGroup.mk F (idealUnit J) = c ∧ (Ideal.absNorm J.val).Coprime m := by
  let Q := Ideal.span {(m : 𝓞 F)}
  have hQ : Q ≠ 0 := by simpa [Q, Ideal.span_singleton_eq_bot] using hm
  have hfin : {P : Ideal (𝓞 F) | P.IsMaximal ∧ Q ≤ P}.Finite := by
    let f (v : HeightOneSpectrum (𝓞 F)) := v.asIdeal
    refine ((Ideal.finite_factors hQ).image f).subset ?_
    rintro P ⟨hP, hle⟩
    exact ⟨⟨P, hP.isPrime, ne_bot_of_le_ne_bot hQ hle⟩,
      Ideal.dvd_iff_le.mpr hle, rfl⟩
  obtain ⟨J, hJ, hcls, htop⟩ := ClassGroup.exists_mk_eq_and_sup_eq_top (K := F) hfin c
  have hJ₀ : J ≠ 0 := by
    intro hj
    simp [hj] at hJ
  have hcond : (conductorOrder F 1).conductor = ⊤ := by
    rw [conductorOne]
    exact conductor_maximal
  let J' : integralIdealsPrimeTo (conductorOrder F 1).conductorModulus :=
    ⟨J, (mem_integralIdealsPrimeTo_conductorModulus_iff _).mpr ⟨hJ₀, by simp [hcond]⟩⟩
  refine ⟨J', ?_, Nat.coprime_of_dvd (fun p hp hpJ hpm => ?_)⟩
  · have he : idealUnit J' = hJ.unit := Units.ext hJ.unit_spec.symm
    rwa [he]
  · obtain ⟨P, hP, hPp, hPJ⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp J hpJ
    have hpm' : (m : ℤ) ∈ P.under ℤ :=
      hPp ▸ (Ideal.mem_span_singleton.mpr (Int.natCast_dvd.mpr hpm))
    have hmem : (m : 𝓞 F) ∈ P := by simpa using hpm'
    exact hP.ne_top (top_unique (htop ▸ sup_le (Ideal.le_of_dvd hPJ)
      ((Ideal.span_singleton_le_iff_mem _).mpr hmem)))

variable (m : ℕ) (hm : m ≠ 0)

abbrev coprimeIdeal (c : ClassGroup (𝓞 F)) := (exists_coprime_class m hm c).choose

theorem count_at_bad (c : ClassGroup (𝓞 F)) (v : HeightOneSpectrum (𝓞 F))
    (hv : (primeBelow F v).val ∣ m) :
    FractionalIdeal.count F v (idealUnit (coprimeIdeal m hm c)).val = 0 := by
  classical
  let J := coprimeIdeal m hm c
  have hJ := ((conductorOrder F 1).mem_integralIdealsPrimeTo_conductorModulus_iff.mp J.prop).1
  change FractionalIdeal.count F v (J.val : FractionalIdeal (𝓞 F)⁰ F) = 0
  rw [FractionalIdeal.count_coe _ _ hJ, Nat.cast_eq_zero]
  by_contra hv'
  have hdiv := (Associates.count_ne_zero_iff_dvd hJ v.irreducible).mp hv'
  have hq : (primeBelow F v).val = TauCeti.rationalPrimeBelow v := rfl
  have hf : 0 < Ideal.inertiaDeg v.asIdeal ℤ := by
    let : v.asIdeal.IsPrime := v.isPrime
    exact Ideal.inertiaDeg_pos ..
  have hn : (primeBelow F v).val ∣ Ideal.absNorm v.asIdeal := by
    rw [hq, TauCeti.absNorm_eq_rationalPrimeBelow_pow]
    exact dvd_pow_self _ hf.ne'
  have hcop := (exists_coprime_class m hm c).choose_spec.2
  exact (primeBelow F v).prop.not_dvd_one
    (hcop.gcd_eq_one ▸ Nat.dvd_gcd (hn.trans (map_dvd Ideal.absNorm hdiv)) hv)

theorem exists_normalized (c : ClassGroup (𝓞 F)) :
    ∃ a : (FiniteAdeleRing (𝓞 F) F)ˣ,
      toFractionalIdeal a = idealUnit (coprimeIdeal m hm c) ∧
      ∀ p : Adelic.Prime, p.val ∣ m → idelePrimeBlocks F a p = 1 := by
  classical
  let J := idealUnit (coprimeIdeal m hm c)
  obtain ⟨a, ha⟩ := toFractionalIdeal_surjective J
  let family (v : HeightOneSpectrum (𝓞 F)) : (v.adicCompletion F)ˣ :=
    if (primeBelow F v).val ∣ m then 1 else
      RestrictedProduct.unitsEquiv (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) a v
  have hf : ∀ᶠ v in Filter.cofinite,
      family v ∈ (Submonoid.ofClass (v.adicCompletionIntegers F)).units := by
    filter_upwards [(RestrictedProduct.unitsEquiv
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) a).prop] with v hv
    by_cases h : (primeBelow F v).val ∣ m
    · simp [family, h]
    · rw [show family v = _ from ite_eq_right h]
      exact hv
  let b : (FiniteAdeleRing (𝓞 F) F)ˣ := RestrictedProduct.mkUnit family hf
  refine ⟨b, ?_, ?_⟩
  · apply Units.ext
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' F (toFractionalIdeal b).ne_zero,
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' F J.ne_zero]
    apply finprod_congr
    intro v
    rw [count_coe_toFractionalIdeal]
    by_cases hv : (primeBelow F v).val ∣ m
    · have hval : b.val v = 1 := by change (family v : v.adicCompletion F) = 1; simp [family, hv]
      rw [adicOrd_def, hval, map_one, WithZero.log_one, neg_zero, count_at_bad m hm c v hv]
    · have he : b.val v = a.val v := by
        change (family v : v.adicCompletion F) = _
        simp only [family, ite_eq_right hv]
        rfl
      rw [adicOrd_def, he, ← adicOrd_def, ← count_coe_toFractionalIdeal, ha]
  · intro p hp
    funext v
    change family v.val = 1
    simp [family, v.prop, hp]

/-- The chosen representative is integral with norm prime to the partner,
and has coordinate one at every finite place over the partner. -/
abbrev normalizedIdele (c : ClassGroup (𝓞 F)) := (exists_normalized m hm c).choose

theorem normalized_class (c : ClassGroup (𝓞 F)) :
    toClassGroup (𝓞 F) F (normalizedIdele m hm c) = c := by
  rw [toClassGroup_apply, (exists_normalized m hm c).choose_spec.1]
  exact (exists_coprime_class m hm c).choose_spec.1


/-- The ideal reading on normalized ideles. Only the valuation of the
embedded block's reduced norm is supplied separately. -/
def normalizedIdealRead
    {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m' D : ℤ}
    {s : StageAt O N M hN m'} {Q : QuadraticBasis F (disc s D)}
    {A : OrbitFibers s.visibility (index s D) N.primeFactors.card (ClassGroup (𝓞 F))}
    (T : TorusWeights.TorusParametrization s D Q A)
    (hm' : s.weights.m = m)
    (ha : ∀ c, T.idele c = normalizedIdele m hm c)
    (hblock : ∀ (a : (FiniteAdeleRing (𝓞 F) F)ˣ) (p : Adelic.Prime),
      idelePrimeBlocks F a p = 1 → (T.embedIdeles a).val p = 1)
    (hnorm : ∀ (c : ClassGroup (𝓞 F)) (p : Adelic.Prime),
      Padic.valuation (TorusWeights.localNrd p ((T.embedIdeles (T.idele c)).val p) : ℚ_[p.val]) =
        ((Ideal.absNorm (coprimeIdeal m hm c).val).factorization p.val : ℤ)) :
    TorusWeights.TorusIdealRead T where
  ideal := coprimeIdeal m hm
  coprime c := hm'.symm ▸ (exists_coprime_class m hm c).choose_spec.2
  fractional c := (congrArg toFractionalIdeal (ha c)).trans
    (exists_normalized m hm c).choose_spec.1
  pic := picOne
  pic_eq c := (picClass_of_max conductorOne _).trans
    (congrArg (fun x : ClassGroup (𝓞 F) => (picOne (F := F)) x)
      (exists_coprime_class m hm c).choose_spec.1)
  valuation := hnorm
  ramified_one c p hp := by
    rw [hblock _ p, map_one]
    rw [ha c]
    exact (exists_normalized m hm c).choose_spec.2 p (hm' ▸ hp)

end ZInQ.Manuscript.RC.O7Assemble
