import ZInQKernel.Contrib.TYZGenus.RingClassBridge

/-! Development file for §11 of `Bridge.lean` (genus field of `ℚ(√−n)`, `n ≡ 3 (mod 4)`). -/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.CMBridgeDev

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Package
  ZInQ.Contrib.TYZGenus.RingClass NumberField TauCeti.ClassFieldTheory
  TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder ZInQ.RouteK.Rank5b
  ZInQ.RouteK.Redei IsDedekindDomain
open scoped nonZeroDivisors

abbrev OK (d : ℕ) [NeZero d] : NumberFieldOrder (QNeg d) := maximalNumberFieldOrder (QNeg d)

def genusBar (d : ℕ) : IntermediateField ℚ Qbar :=
  if h : d = 0 then ⊥ else
    haveI : NeZero d := ⟨h⟩; ((genusField (OK d)).restrictScalars ℚ).map (embed d)

def GenusFieldLeLni : Prop := ∀ e : ℕ, e % 8 = 7 → Squarefree e → genusBar e ≤ Lni e

/-- The Picard class (Tau Ceti) of an ideal for the maximal order is its ideal class. -/
theorem picClass_maximal {K : Type} [Field K] [NumberField K]
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
  sorry


section Genus

variable {n : ℕ} [NeZero n]

/-- The square-root generators of `L_n(i)`: `−1` and the primes `p ∣ n`. -/
def sqrtSet (n : ℕ) : Finset ℤ := insert (-1) (n.primeFactors.image (fun p : ℕ => (p : ℤ)))

/-- `K_n(i, √p : p ∣ n) ⊆ K_nˢ`. -/
def genusAmb (n : ℕ) [NeZero n] : IntermediateField (QNeg n) (SeparableClosure (QNeg n)) :=
  ⨆ a ∈ sqrtSet n, adjSqrt (QNeg n) a

instance : FiniteDimensional (QNeg n) (genusAmb n) := by unfold genusAmb; infer_instance
instance : Normal (QNeg n) (genusAmb n) := by unfold genusAmb; infer_instance
instance : IsGalois (QNeg n) (genusAmb n) := IsGalois.mk

/-- **Genus characters at a prime split in `K_n(i, √p : p ∣ n)`**: if `−1` and every `p ∣ n` are
squares modulo `𝔭 ∌ 2n`, then `χ_q([𝔭]) = 1` for every `q ∣ n` (`|O/𝔭| ≡ 1 (mod 4)` and
`(|O/𝔭| / q) = (q / |O/𝔭|) = 1`, quadratic reciprocity in Mathlib's finite-field form). -/
theorem chi_eq_one_of_isSquare (hn : Odd n) (hsq : Squarefree n)
    (𝔭 : HeightOneSpectrum (𝓞 (QNeg n)))
    (h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal)
    (hm1 : IsSquare (((-1 : ℤ) : 𝓞 (QNeg n)) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal))
    (hp : ∀ p ∈ n.primeFactors, IsSquare ((((p : ℤ) : 𝓞 (QNeg n))) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal))
    (q : n.primeFactors) :
    chi n q (ClassGroup.mk0 ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩) = 1 := by
  have hqp := Nat.prime_of_mem_primeFactors q.2
  haveI := Fact.mk hqp
  letI := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
  letI := Fintype.ofFinite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal)
  set F := 𝓞 (QNeg n) ⧸ 𝔭.asIdeal
  have h2 : (2 : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := fun h => h2n (by
    push_cast; exact 𝔭.asIdeal.mul_mem_right _ h)
  have hchar : ringChar F ≠ 2 := fun hc => h2 (by
    have : ((2 : ℕ) : F) = 0 := by rw [← hc]; exact ringChar.Nat.cast_ringChar
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
    simpa using this)
  have hq2 : (q : ℕ) ≠ 2 := by
    rintro h
    have := Nat.dvd_of_mem_primeFactors q.2
    rw [h] at this
    exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 this)
  have hqF : ((q : ℕ) : F) ≠ 0 := by
    intro h0
    apply h2n
    obtain ⟨m, hm⟩ := Nat.dvd_of_mem_primeFactors q.2
    have h1 : ((q : ℕ) : 𝓞 (QNeg n)) ∈ 𝔭.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]; simpa using h0
    rw [hm]; push_cast
    exact 𝔭.asIdeal.mul_mem_left _ (𝔭.asIdeal.mul_mem_right _ h1)
  have hN : Ideal.absNorm 𝔭.asIdeal = Fintype.card F := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hodd : Fintype.card F % 2 = 1 := Nat.odd_iff.mp (FiniteField.odd_card_of_char_ne_two hchar)
  have h4 : Fintype.card F % 4 = 1 := by
    have := FiniteField.isSquare_neg_one_iff.1 (by simpa using hm1)
    omega
  have hsqq := (FiniteField.isSquare_odd_prime_iff hchar hq2).1 (by simpa using hp q q.2)
  rw [ZMod.χ₄_nat_one_mod_four h4] at hsqq
  simp only [Int.cast_one, one_mul] at hsqq
  have hsquare : IsSquare ((Fintype.card F : ℕ) : ZMod q) := by
    by_contra hns
    exact hsqq (quadraticChar_neg_one_iff_not_isSquare.2 hns)
  have hqN : ¬ (q : ℕ) ∣ Ideal.absNorm 𝔭.asIdeal := by
    rw [hN]
    intro hd
    obtain ⟨k, hk, hcard⟩ := FiniteField.card F (ringChar F)
    have hpr : (ringChar F).Prime := hk
    rw [hcard] at hd
    have := (Nat.prime_dvd_prime_iff_eq hqp hpr).1 (hqp.dvd_of_dvd_pow hd)
    apply hqF
    rw [this]
    exact ringChar.Nat.cast_ringChar
  rw [chi_mk0 n hn hsq q _ hqN]
  simp only [legBit]
  rw [if_pos (by rw [hN]; exact_mod_cast hsquare)]
  rfl

/-- Transfer along `conductorOrder K 1 = maximal order`, then genus theory
(`picSquares_eq_iInf_ker_chi`). -/
theorem picClass_mem_picSquares (hn : Odd n) (hsq : Squarefree n) (h1 : 1 < n)
    (O : NumberFieldOrder (QNeg n)) (hO : O = maximalNumberFieldOrder (QNeg n))
    (J : integralIdealsPrimeTo O.conductorModulus) (hJ0 : (J : Ideal (𝓞 (QNeg n))) ∈ (Ideal _)⁰)
    (hchi : ∀ q, chi n q (ClassGroup.mk0 ⟨(J : Ideal (𝓞 (QNeg n))), hJ0⟩) = 1) :
    O.picClass J ∈ picSquares O := by
  subst hO
  rw [picClass_maximal J hJ0, picSquares_eq_iInf_ker_chi n hn hsq h1]
  exact Subgroup.mem_iInf.2 fun q => hchi q

/-- **The genus field of `K_n`, `n ≡ 3 (mod 4)` squarefree, lies in `K_n(i, √p : p ∣ n)`** (Bauer). -/
theorem genusField_le_genusAmb (hn : n % 4 = 3) (hsq : Squarefree n) (h1 : 1 < n) :
    genusField (maximalNumberFieldOrder (QNeg n)) ≤ genusAmb n := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hG : genusField (maximalNumberFieldOrder (QNeg n)) =
      ringSubfield (picSquares (conductorOrder (QNeg n) 1)) := by
    rw [← conductorOrder_one]; rfl
  rw [hG]
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
  rw [mem_splitSet_iff (conductorOrder (QNeg n) 1) _ ⟨_, hJ⟩ 𝔭 rfl]
  have hsplit : ∀ a ∈ sqrtSet n, 𝔭 ∈ splitSet (QNeg n) (adjSqrt (QNeg n) a) := fun a ha =>
    splitSet_anti (le_iSup₂ (f := fun a _ => adjSqrt (QNeg n) a) a ha) h𝔭
  have hm1 := (mem_splitSet_adjSqrt_iff 𝔭 (a := -1) (by
    intro h; apply h2
    have : -((2 * (-1) : ℤ) : 𝓞 (QNeg n)) ∈ 𝔭.asIdeal := 𝔭.asIdeal.neg_mem h
    simpa using this)).1 (hsplit (-1) (Finset.mem_insert_self _ _))
  have hp : ∀ p ∈ n.primeFactors,
      IsSquare ((((p : ℤ) : 𝓞 (QNeg n))) : 𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := by
    intro p hp
    refine (mem_splitSet_adjSqrt_iff 𝔭 (a := p) ?_).1
      (hsplit p (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp)))
    intro h; apply h2n
    obtain ⟨n', hn'⟩ := Nat.dvd_of_mem_primeFactors hp
    have hcast : ((2 * n : ℕ) : 𝓞 (QNeg n)) =
        ((2 * (p : ℤ) : ℤ) : 𝓞 (QNeg n)) * (n' : 𝓞 (QNeg n)) := by
      rw [hn']; push_cast; ring
    rw [hcast]
    exact 𝔭.asIdeal.mul_mem_right _ h
  exact picClass_mem_picSquares hodd hsq h1 _ (conductorOrder_one _) ⟨_, hJ⟩
    (mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot)
    (chi_eq_one_of_isSquare hodd hsq 𝔭 h2n hm1 hp)

/-! ### From `K_nˢ` to `ℚ̄` -/

theorem embed_sqrtK_mem_Lni {a : ℤ} (ha : a ∈ sqrtSet n) : embed n (sqrtK (QNeg n) a) ∈ Lni n := by
  apply IntermediateField.subset_adjoin
  have hs : embed n (sqrtK (QNeg n) a) ^ 2 = (a : Qbar) := by rw [← map_pow, sqrtK_sq, map_intCast]
  rcases Finset.mem_insert.1 ha with rfl | ha
  · left; simpa using hs
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
    right; exact ⟨p, hp, by simpa using hs⟩

theorem embed_omega_mem_Lni (hsq : Squarefree n) :
    embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega) ∈ Lni n := by
  have hroot : ∀ p ∈ n.primeFactors, ∃ r : Qbar, r ^ 2 = (p : Qbar) := fun p _ =>
    IsAlgClosed.exists_pow_nat_eq _ two_pos
  choose r hr using hroot
  set y := iQ * ∏ p ∈ n.primeFactors.attach, r p.1 p.2
  have hy : y ∈ Lni n := mul_mem (iQ_mem_Lni n) (prod_mem fun p _ =>
    IntermediateField.subset_adjoin _ _ (Or.inr ⟨p.1, p.2, hr _ _⟩))
  have hy2 : y ^ 2 = -(n : Qbar) := by
    rw [mul_pow, iQ_sq, ← Finset.prod_pow]
    have : ∏ p ∈ n.primeFactors.attach, r p.1 p.2 ^ 2 = ∏ p ∈ n.primeFactors.attach, ((p.1 : ℕ) : Qbar) :=
      Finset.prod_congr rfl fun p _ => hr _ _
    rw [this, Finset.prod_attach n.primeFactors (fun p => ((p : ℕ) : Qbar)), ← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree hsq]
    ring
  have hw2 : (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)) ^ 2 =
      -(n : Qbar) := by
    rw [← map_pow, ← map_pow]
    simp [QuadraticAlgebra.omega_pow_two_eq_add]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hw2.trans hy2.symm) with h | h
  · rw [h]; exact hy
  · rw [h]; exact neg_mem hy

theorem embed_algebraMap_mem_Lni (hsq : Squarefree n) (k : QNeg n) :
    embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) k) ∈ Lni n := by
  rw [algebraMap_eq_re_im, map_add, map_mul, AlgHom.commutes, AlgHom.commutes]
  exact add_mem (IntermediateField.algebraMap_mem _ _)
    (mul_mem (IntermediateField.algebraMap_mem _ _) (embed_omega_mem_Lni hsq))

/-- `L_n(i)` pulled back to `K_nˢ`, as a field over `K_n`. -/
def LniK (n : ℕ) [NeZero n] (hsq : Squarefree n) :
    IntermediateField (QNeg n) (SeparableClosure (QNeg n)) :=
  { ((Lni n).comap (embed n)) with
    algebraMap_mem' := fun k => embed_algebraMap_mem_Lni hsq k }

theorem mem_LniK (hsq : Squarefree n) {x : SeparableClosure (QNeg n)} :
    x ∈ LniK n hsq ↔ embed n x ∈ Lni n := Iff.rfl

theorem genusAmb_le_LniK (hsq : Squarefree n) : genusAmb n ≤ LniK n hsq := by
  refine iSup₂_le fun a ha => ?_
  rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
  exact (mem_LniK hsq).2 (embed_sqrtK_mem_Lni ha)

/-- **Genus theory for `n ≡ 7 (mod 8)`** (cm-numeric's leaf `GenusFieldLeLni`), proved. -/
theorem genusFieldLeLni : GenusFieldLeLni := by
  intro e he hsq
  haveI : NeZero e := ⟨by omega⟩
  have hle := (genusField_le_genusAmb (n := e) (by omega) hsq (by omega)).trans
    (genusAmb_le_LniK hsq)
  simp only [genusBar, NeZero.ne e, ↓reduceDIte]
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_LniK hsq).1 (hle hx)

end Genus

end ZInQ.Contrib.TYZGenus.CMBridgeDev
