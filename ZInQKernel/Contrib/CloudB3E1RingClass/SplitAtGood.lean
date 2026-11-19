import ZInQKernel.Contrib.CloudB3E1RingClass.KRVal

/-!
# Good primes split in `K = ℚ(s)`, at every Frobenius place

Manuscript `diophantine_zq.tex`, tex 3566 ("for split `r`"), with the definition of good primes
(lane RC17/RC27's `GoodPrime`: `r` prime, not excluded, with an arithmetic Frobenius fixing `K`).

For a quadratic `K = ℚ(s) ⊂ ℚ̄`, a good prime `r` not dividing the discriminant splits in `K`. The
prime `𝔯 = v ∩ 𝒪_K` under any Frobenius place `v` over `r` has a conjugate `𝔯̄ ≠ 𝔯` with
`r𝒪_K = 𝔯𝔯̄` (`exists_split_of_good`). This is the input that turns the connecting map `δ` at a
split pair into the interface's `δ` on the places `kummerPlaces r`.

Proof. `r` is unramified (it does not divide the discriminant), so `r` is inert or split
(`isPrincipal_or_split`). Suppose it is inert. A Frobenius `h` at a prime `P` over `r` fixing `K`
gives `x ≡ x^r` modulo `P ∩ 𝒪_K = r𝒪_K` for every `x ∈ 𝒪_K`, so every element of the field
`𝒪_K/r𝒪_K` lies in `𝐅_r` (`exists_zmod_of_pow_eq_self`). But that field has `r²` elements.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.TateWiring ZInQ.Manuscript.RC.WitnessSpec
open ZInQ.Contrib.ChebFD.C10 (Qbar Zbar GQ IsFrobAt)

variable (s : Qbar)

/-- The prime of `K = ℚ(s)` under a Frobenius place. Kind: definition. -/
def placeRestrict {r : ℕ} [Fact r.Prime] (v : kummerPlaces r) : HeightOneSpectrum (𝓞 (quadField s)) :=
  v.2.restrictHeightOne (quadField s).val

theorem placeRestrict_under {r : ℕ} [Fact r.Prime] (v : kummerPlaces r) :
    (placeRestrict s v).asIdeal.under ℤ = Ideal.span {(r : ℤ)} :=
  v.2.restrictPrime_under (quadField s).val

/-- **A Frobenius at `r` fixing `K` forces `r` not inert.** If `r𝒪_K` is prime and some
Frobenius at a prime over `r` fixes `K`, then `|𝒪_K/r𝒪_K| ≤ r`. Kind: PROVED. -/
theorem not_inert_of_frob (hK : Module.finrank ℚ (quadField s) = 2) {r : ℕ} [hr : Fact r.Prime]
    {h : GQ} (w : FrobeniusPlace h r) (hs : h s = s)
    (hinert : (Ideal.span {((r : ℤ) : 𝓞 (quadField s))}).IsMaximal) : False := by
  classical
  set R := 𝓞 (quadField s)
  set I : Ideal R := Ideal.span {((r : ℤ) : R)}
  let e : quadField s →ₐ[ℚ] Qbar := (quadField s).val
  -- every `x ∈ 𝒪_K` satisfies `x^r ≡ x` modulo `I`
  have hq_le : I ≤ w.restrictPrime e := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    have hm : (r : ℤ) ∈ (w.restrictPrime e).under ℤ := by
      rw [w.restrictPrime_under e]; exact Ideal.mem_span_singleton_self _
    simpa using hm
  have hq_eq : w.restrictPrime e = I :=
    (hinert.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hq_le).symm
  have hcong : ∀ x : R, x ^ r - x ∈ I := by
    intro x
    rw [← neg_sub, ← hq_eq]
    refine neg_mem ?_
    change FrobeniusPlace.integersMap e (x - x ^ r) ∈ w.prime
    apply w.frob (FrobeniusPlace.integersMap e x) (FrobeniusPlace.integersMap e (x - x ^ r))
    have hx : ((FrobeniusPlace.integersMap e x : Zbar) : Qbar) = e (x : quadField s) :=
      algebraMap_galRestrict'_apply ℤ (𝓞 (quadField s)) Zbar e x
    have hxr : ((FrobeniusPlace.integersMap e (x - x ^ r) : Zbar) : Qbar) =
        e ((x - x ^ r : R) : quadField s) :=
      algebraMap_galRestrict'_apply ℤ (𝓞 (quadField s)) Zbar e (x - x ^ r)
    rw [hxr, hx]
    have hfix : h (e (x : quadField s)) = e (x : quadField s) :=
      fix_of_mem_quadField hs (x : quadField s).2
    rw [hfix]
    push_cast
    rw [map_sub, map_pow]
  -- the residue field `𝒪_K/I`
  have : I.IsMaximal := hinert
  let _ : Field (R ⧸ I) := Ideal.Quotient.field I
  have hchar : CharP (R ⧸ I) r := by
    refine (CharP.charP_iff_prime_eq_zero hr.out).mpr ?_
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact_mod_cast Ideal.mem_span_singleton_self ((r : ℤ) : R)
  have hsurj : Function.Surjective (ZMod.castHom (dvd_refl r) (R ⧸ I)) := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine exists_zmod_of_pow_eq_self _ ?_
    rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hcong x
  have hcard_le : Nat.card (R ⧸ I) ≤ r := by
    have := Nat.card_le_card_of_surjective _ hsurj
    rwa [Nat.card_zmod] at this
  have hnorm : Nat.card (R ⧸ I) = r ^ 2 := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton,
      show ((r : ℤ) : R) = algebraMap ℤ R (r : ℤ) by simp, Algebra.norm_algebraMap,
      RingOfIntegers.rank, hK, Int.natAbs_pow, Int.natAbs_natCast]
  rw [hnorm] at hcard_le
  have h1 := hr.out.one_lt
  nlinarith

/-- **A good prime splits in `K` at every Frobenius place** (tex 3566): for `K = ℚ(s)`
quadratic, `r` good and not dividing the discriminant, the prime `𝔯 = v ∩ 𝒪_K` under any Frobenius
place `v` over `r` has a conjugate `𝔯̄ ≠ 𝔯` with `r𝒪_K = 𝔯𝔯̄`. Kind: PROVED. -/
theorem exists_split_of_good (hK : Module.finrank ℚ (quadField s) = 2) {E : WeierstrassCurve ℚ}
    {Sexc : Finset ℕ} {r : ℕ} [hr : Fact r.Prime] (hgood : GoodPrime E s Sexc r)
    (hdisc : ¬ (r : ℤ) ∣ discr (quadField s)) (v : kummerPlaces r) :
    ∃ Q : HeightOneSpectrum (𝓞 (quadField s)), Q ≠ placeRestrict s v ∧
      Ideal.span {((r : ℤ) : 𝓞 (quadField s))} = (placeRestrict s v).asIdeal * Q.asIdeal := by
  have hvq := placeRestrict_under s v
  have he : (placeRestrict s v).asIdeal.ramificationIdx ℤ = 1 := by
    have hU := (not_dvd_discr_iff_forall_liesOver (quadField s) (𝓞 (quadField s))
      (Nat.prime_iff_prime_int.mp hr.out)).mp hdisc (placeRestrict s v).asIdeal
      (placeRestrict s v).isMaximal ⟨hvq.symm⟩
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  rcases isPrincipal_or_split hK (placeRestrict s v) hr.out hvq he with hin | ⟨Q, hne, -, hmul⟩
  · exfalso
    obtain ⟨g, hg, hgs⟩ := hgood.2.2.2.2
    have hmax : (Ideal.span {((r : ℤ) : 𝓞 (quadField s))}).IsMaximal :=
      hin ▸ (placeRestrict s v).isMaximal
    exact not_inert_of_frob s hK (FrobeniusPlace.ofIsFrobAt hg) hgs hmax
  · exact ⟨Q, hne, hmul.symm⟩

end ZInQ.Contrib.CloudB3E1RingClass
