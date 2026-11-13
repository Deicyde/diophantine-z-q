import ZInQKernel.Contrib.TYZGenus.RingClassGalois
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory IsDedekindDomain Polynomial

noncomputable section
namespace ZInQ.Contrib.TYZGenus.RingClass

section SqrtInt

variable (K : Type) [Field K] [NumberField K] (a : ℤ)

/-- A square root of the integer `a` in `Kˢ`. -/
def sqrtK : SeparableClosure K :=
  (IsSepClosed.exists_pow_nat_eq (k := SeparableClosure K) (a : SeparableClosure K) 2).choose

theorem sqrtK_sq : sqrtK K a ^ 2 = (a : SeparableClosure K) :=
  (IsSepClosed.exists_pow_nat_eq (k := SeparableClosure K) (a : SeparableClosure K) 2).choose_spec

theorem isIntegral_sqrtK : IsIntegral K (sqrtK K a) :=
  ⟨X ^ 2 - C (a : K), monic_X_pow_sub_C _ two_ne_zero, by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sqrtK_sq, map_intCast, sub_self]⟩

/-- `K(√a) ⊆ Kˢ`. -/
abbrev adjSqrt : IntermediateField K (SeparableClosure K) := IntermediateField.adjoin K {sqrtK K a}

instance : FiniteDimensional K (adjSqrt K a) :=
  IntermediateField.adjoin.finiteDimensional (isIntegral_sqrtK K a)

instance : NumberField (adjSqrt K a) := NumberField.of_module_finite K (adjSqrt K a)

instance : Normal K (adjSqrt K a) := by
  rw [IntermediateField.normal_iff_forall_map_le']
  intro g
  rw [IntermediateField.adjoin_map, Set.image_singleton, IntermediateField.adjoin_le_iff,
    Set.singleton_subset_iff]
  have h : g (sqrtK K a) ^ 2 = sqrtK K a ^ 2 := by rw [← map_pow, sqrtK_sq, map_intCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · simp only [AlgEquiv.coe_toAlgHom, h, SetLike.mem_coe]
    exact IntermediateField.mem_adjoin_simple_self K _
  · simp only [AlgEquiv.coe_toAlgHom, h, SetLike.mem_coe]
    exact neg_mem (IntermediateField.mem_adjoin_simple_self K _)

instance : IsGalois K (adjSqrt K a) := IsGalois.mk

theorem genS_sq : (IntermediateField.AdjoinSimple.gen K (sqrtK K a)) ^ 2 = (a : adjSqrt K a) :=
  Subtype.ext (by simp [sqrtK_sq])

/-- `√a` as an element of `𝓞_{K(√a)}`. -/
def sqrtO : 𝓞 (adjSqrt K a) :=
  ⟨IntermediateField.AdjoinSimple.gen K (sqrtK K a), by
    refine ⟨X ^ 2 - C a, monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, genS_sq, eq_intCast, sub_self]⟩

theorem sqrtO_sq : sqrtO K a ^ 2 = (a : 𝓞 (adjSqrt K a)) := by
  apply RingOfIntegers.ext
  simp only [RingOfIntegers.coe_eq_algebraMap, map_pow, map_intCast]
  exact genS_sq K a

theorem adjoin_sqrtO_eq_top :
    Algebra.adjoin K {algebraMap (𝓞 (adjSqrt K a)) (adjSqrt K a) (sqrtO K a)} = ⊤ :=
  (IntermediateField.adjoin.powerBasis (isIntegral_sqrtK K a)).adjoin_gen_eq_top

variable {K a}

/-- Primes `Q` of `𝓞_{K(√a)}` not containing `2a` are unramified over `𝓞_K`. -/
theorem isUnramifiedAt_sqrt (Q : Ideal (𝓞 (adjSqrt K a))) [Q.IsPrime]
    (h2 : ((2 * a : ℤ) : 𝓞 (adjSqrt K a)) ∉ Q) : Algebra.IsUnramifiedAt (𝓞 K) Q := by
  refine not_dvd_differentIdeal_iff.1 fun hdvd => h2 ?_
  have hmem := TauCeti.natCast_mul_mem_differentIdeal_of_pow_eq (A := 𝓞 K) (K := K)
    (L := adjSqrt K a) (B := 𝓞 (adjSqrt K a)) (adjoin_sqrtO_eq_top K a) (n := 2) (a := (a : 𝓞 K))
    (by rw [sqrtO_sq, map_intCast])
  have := Ideal.le_of_dvd hdvd hmem
  have h' : ((2 * a : ℤ) : 𝓞 (adjSqrt K a)) =
      ((2 : ℕ) : 𝓞 (adjSqrt K a)) * algebraMap (𝓞 K) (𝓞 (adjSqrt K a)) (a : 𝓞 K) := by
    simp
  rw [h']
  exact this

/-- **The Frobenius on `√a`** (Euler's criterion form): an arithmetic Frobenius `σ` at `Q ∌ 2a`
with odd residue norm `q` fixes `√a` iff `a^((q−1)/2) ≡ 1` modulo `Q ∩ 𝓞_K`. -/
theorem smul_sqrtO_eq_iff (Q : Ideal (𝓞 (adjSqrt K a))) [Q.IsPrime]
    (h2 : ((2 * a : ℤ) : 𝓞 (adjSqrt K a)) ∉ Q) (σ : adjSqrt K a ≃ₐ[K] adjSqrt K a)
    (hσ : IsArithFrobAt (𝓞 K) σ Q) (hq : Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) % 2 = 1) :
    σ • sqrtO K a = sqrtO K a ↔
      (a : 𝓞 K) ^ (Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) / 2) - 1 ∈ Q.under (𝓞 K) := by
  set q := Nat.card (𝓞 K ⧸ Q.under (𝓞 K))
  set s := sqrtO K a
  have h := hσ s
  simp only [MulSemiringAction.toAlgHom_apply] at h
  have hq' : q = 2 * (q / 2) + 1 := by omega
  set u : 𝓞 (adjSqrt K a) := (a : 𝓞 (adjSqrt K a)) ^ (q / 2)
  have hpow : s ^ q = s * u := by
    rw [hq', pow_succ, pow_mul, sqrtO_sq, mul_comm]
  rw [hpow] at h
  have hu : algebraMap (𝓞 K) (𝓞 (adjSqrt K a)) ((a : 𝓞 K) ^ (q / 2) - 1) = u - 1 := by simp [u]
  have hsQ : s ∉ Q := fun hs => h2 (by
    have : s * s ∈ Q := Q.mul_mem_left _ hs
    rw [← pow_two, sqrtO_sq] at this
    push_cast
    exact Q.mul_mem_left _ this)
  have hsq : (σ • s) ^ 2 = s ^ 2 := by
    rw [← smul_pow', sqrtO_sq]
    have := map_intCast (MulSemiringAction.toRingHom (adjSqrt K a ≃ₐ[K] adjSqrt K a)
      (𝓞 (adjSqrt K a)) σ) a
    exact this
  rw [Ideal.under_def, Ideal.mem_comap, hu]
  constructor
  · intro hfix
    rw [hfix] at h
    have : s * (1 - u) ∈ Q := by rw [mul_sub, mul_one]; exact h
    rcases Ideal.IsPrime.mem_or_mem inferInstance this with h1 | h1
    · exact absurd h1 hsQ
    · rw [← neg_sub]; exact Q.neg_mem_iff.2 h1
  · intro h1
    have h3 : σ • s - s ∈ Q := by
      have : σ • s - s = (σ • s - s * u) + s * (u - 1) := by ring
      rw [this]; exact Q.add_mem h (Q.mul_mem_left _ h1)
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h4 | h4
    · exact h4
    · exfalso
      rw [h4] at h3
      apply h2
      have : (-s - s) * s ∈ Q := Q.mul_mem_right _ h3
      have e : (-s - s) * s = -((2 * a : ℤ) : 𝓞 (adjSqrt K a)) := by
        have := sqrtO_sq K a
        push_cast
        linear_combination (-2 : 𝓞 (adjSqrt K a)) * this
      rw [e] at this
      exact Q.neg_mem_iff.1 this

theorem eq_one_iff_smul_sqrtO (σ : adjSqrt K a ≃ₐ[K] adjSqrt K a) :
    σ = 1 ↔ σ • sqrtO K a = sqrtO K a := by
  constructor
  · rintro rfl; exact one_smul _ _
  · intro hfix
    have hfix' : σ (IntermediateField.AdjoinSimple.gen K (sqrtK K a)) =
        IntermediateField.AdjoinSimple.gen K (sqrtK K a) := congrArg Subtype.val hfix
    apply AlgEquiv.coe_algHom_injective
    apply IntermediateField.adjoin_algHom_ext
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hfix'

/-- **Splitting in `K(√a)`**: a prime `𝔭 ∌ 2a` of `K` splits completely in `K(√a)` iff `a` is a
square modulo `𝔭`. -/
theorem mem_splitSet_adjSqrt_iff (𝔭 : HeightOneSpectrum (𝓞 K))
    (h2 : ((2 * a : ℤ) : 𝓞 K) ∉ 𝔭.asIdeal) :
    𝔭 ∈ splitSet K (adjSqrt K a) ↔ IsSquare ((a : 𝓞 K ⧸ 𝔭.asIdeal)) := by
  have h2Q : ∀ (Q : Ideal (𝓞 (adjSqrt K a))) [Q.LiesOver 𝔭.asIdeal],
      ((2 * a : ℤ) : 𝓞 (adjSqrt K a)) ∉ Q := by
    intro Q _ h
    apply h2
    have : algebraMap (𝓞 K) (𝓞 (adjSqrt K a)) ((2 * a : ℤ) : 𝓞 K) ∈ Q := by rwa [map_intCast]
    rwa [← Ideal.mem_comap, ← Ideal.under_def, ← Ideal.over_def Q 𝔭.asIdeal] at this
  have hur : ∀ (Q : Ideal (𝓞 (adjSqrt K a))) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q := fun Q _ _ => isUnramifiedAt_sqrt Q (h2Q Q)
  have h2' : (2 : 𝓞 K) ∉ 𝔭.asIdeal := fun h => h2 (by
    rw [Int.cast_mul, Int.cast_two]; exact 𝔭.asIdeal.mul_mem_right _ h)
  obtain ⟨Q, hQp, hQo⟩ := (inferInstance : Nonempty (𝔭.asIdeal.primesOver (𝓞 (adjSqrt K a))))
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt K Q hQ
  have hA := artinSymbol_eq_mk_of_isArithFrobAt 𝔭.asIdeal hur Q σ hσ
  have hunder : Q.under (𝓞 K) = 𝔭.asIdeal := (Ideal.over_def Q 𝔭.asIdeal).symm
  have hodd := card_quot_odd 𝔭 h2'
  have hkey := smul_sqrtO_eq_iff Q (h2Q Q) σ hσ (by rwa [hunder])
  rw [hunder] at hkey
  change (𝔭.asIdeal.primesOver (𝓞 (adjSqrt K a))).ncard = Module.finrank K (adjSqrt K a) ↔ _
  rw [← artinSymbol_eq_one_iff_ncard_primesOver_eq_finrank 𝔭.asIdeal hur, hA,
    ConjClasses.one_eq_mk_one, ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left,
    eq_one_iff_smul_sqrtO, hkey]
  letI := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
  letI := Fintype.ofFinite (𝓞 K ⧸ 𝔭.asIdeal)
  have hchar : ringChar (𝓞 K ⧸ 𝔭.asIdeal) ≠ 2 := fun hc => h2' (by
    have : ((2 : ℕ) : 𝓞 K ⧸ 𝔭.asIdeal) = 0 := by rw [← hc]; exact ringChar.Nat.cast_ringChar
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
    simpa using this)
  have ha0 : ((a : 𝓞 K ⧸ 𝔭.asIdeal)) ≠ 0 := fun h0 => h2 (by
    rw [Int.cast_mul]
    refine 𝔭.asIdeal.mul_mem_left _ ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast]
    exact h0)
  rw [FiniteField.isSquare_iff hchar ha0, ← Nat.card_eq_fintype_card,
    ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_intCast, map_one, sub_eq_zero]

end SqrtInt

section SqrtTwo

open ZInQ.RouteK.Rank5b ZInQ.RouteK.Redei ZInQ.Contrib.TYZDecomp.CurveA

variable {d : ℕ} [NeZero d]

/-- For `d ≡ 1 (mod 4)`, `Tr(y) = 2 re y` is even for `y ∈ 𝓞_{K_d}`. -/
theorem even_two_re (hd : d % 4 = 1) (y : 𝓞 (QNeg d)) :
    ∃ t : ℤ, 2 * (y : QNeg d).re = 2 * t := by
  obtain ⟨m, hm⟩ := exists_two_re y
  obtain ⟨k, hk⟩ := exists_two_re (y * sqrtNeg d)
  have hN := normZ_eq_re_im y
  have hre : ((y * sqrtNeg d : 𝓞 (QNeg d)) : QNeg d).re = -(d : ℚ) * (y : QNeg d).im := by
    simp [RingOfIntegers.coe_eq_algebraMap, coe_sqrtNeg]
  rw [hre] at hk
  have hZ : (d : ℤ) * m ^ 2 + k ^ 2 = 4 * d * Algebra.norm ℤ y := by
    have : (d : ℚ) * (m : ℚ) ^ 2 + (k : ℚ) ^ 2 = 4 * d * (Algebra.norm ℤ y : ℚ) := by
      rw [← hm, ← hk, hN]; ring
    exact_mod_cast this
  have h4 := congrArg (fun t : ℤ => (t : ZMod 4)) hZ
  push_cast at h4
  have hd4 : ((d : ℕ) : ZMod 4) = 1 := by rw [← ZMod.natCast_mod, hd]; rfl
  rw [hd4] at h4
  have key : ∀ x y z : ZMod 4, 1 * x ^ 2 + y ^ 2 = 4 * 1 * z → x ^ 2 = 0 := by decide
  have hm2 := key _ _ _ h4
  have h4m : (4 : ℤ) ∣ m ^ 2 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (m ^ 2) 4).1 (by push_cast; exact hm2)
    exact_mod_cast this
  have hev : Even m := (Int.even_pow.1 (even_iff_two_dvd.2 (dvd_trans ⟨2, rfl⟩ h4m))).1
  obtain ⟨t, ht⟩ := hev
  exact ⟨t, by rw [hm, ht]; push_cast; ring⟩

/-- For `d ≡ 1 (mod 4)`, norms of elements of `O_{d,4} = ℤ + 4𝓞_K` are `≡ a² (mod 8)`. -/
theorem norm_of_mem_O4_mod8 (hd : d % 4 = 1) (β : 𝓞 (QNeg d))
    (hβ : β ∈ (O4 d).toRingOfIntegers) : ∃ a c : ℤ, Algebra.norm ℤ β = a ^ 2 + 8 * c := by
  obtain ⟨a, y, hy⟩ := (NumberFieldOrder.mem_toRingOfIntegers _).1 hβ
  obtain ⟨t, ht⟩ := even_two_re hd y
  refine ⟨a, a * t + 2 * Algebra.norm ℤ y, ?_⟩
  have h1 := normZ_eq_re_im β
  have h2 := normZ_eq_re_im y
  rw [hy] at h1
  have hre : ((a : QNeg d) + ((4 : ℕ) : QNeg d) * (y : QNeg d)).re = a + 4 * (y : QNeg d).re := by
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast,
      QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast]
    push_cast
    ring
  have him : ((a : QNeg d) + ((4 : ℕ) : QNeg d) * (y : QNeg d)).im = 4 * (y : QNeg d).im := by
    simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_intCast,
      QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast]
    push_cast
    ring
  rw [hre, him] at h1
  have hret : (y : QNeg d).re = t := by linarith
  have : ((Algebra.norm ℤ β : ℤ) : ℚ) =
      ((a ^ 2 + 8 * (a * t + 2 * Algebra.norm ℤ y) : ℤ) : ℚ) := by
    push_cast
    rw [h1, h2, hret]
    ring
  exact_mod_cast this

/-- **`√2 ∈ H_{d,4}`** for `d ≡ 1 (mod 4)`: `K_d(√2) ⊆ H_{d,4}` (TYZ Proposition 3.2(1):
`H'_d(√2) = H_{d,4}`). -/
theorem adjSqrt_two_le_H4 (hd : d % 4 = 1) : adjSqrt (QNeg d) 2 ≤ H4 d := by
  rw [H4_eq_ringSubfield]
  refine le_of_splitSet_diff_subset _ finite_two_conductor_primes ?_
  rintro 𝔭 ⟨h𝔭, hT⟩
  have hT1 : ¬ (O4 d).conductor ≤ 𝔭.asIdeal := fun h => hT (le_trans Ideal.mul_le_left h)
  have h2 : (2 : 𝓞 (QNeg d)) ∉ 𝔭.asIdeal := fun h =>
    hT (le_trans Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h))
  have h22 : ((2 * 2 : ℤ) : 𝓞 (QNeg d)) ∉ 𝔭.asIdeal := fun h => h2 (by
    rw [Int.cast_mul, Int.cast_two] at h
    exact (Ideal.IsPrime.mem_or_mem inferInstance h).elim id id)
  have hJ := mem_primeTo_of_not_le 𝔭 hT1
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
    Ideal (𝓞 (QNeg d))).IsMaximal := 𝔭.isMaximal
  have h1 := (mem_splitSet_iff (O4 d) ⊥ ⟨_, hJ⟩ 𝔭 rfl).1 h𝔭
  rw [Subgroup.mem_bot, picClass_eq_one_iff] at h1
  obtain ⟨β, hβ, hspan⟩ := h1
  obtain ⟨a, c, hN⟩ := norm_of_mem_O4_mod8 hd β hβ
  have hq : Nat.card (𝓞 (QNeg d) ⧸ 𝔭.asIdeal) = (Algebra.norm ℤ β).natAbs := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    change Ideal.absNorm (((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
      Ideal (𝓞 (QNeg d)))) = _
    rw [hspan, Ideal.absNorm_span_singleton]
  have hodd := card_quot_odd 𝔭 h2
  have hnn := normZ_nonneg (n := d) β
  rw [mem_splitSet_adjSqrt_iff 𝔭 h22]
  letI := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 (QNeg d) ⧸ 𝔭.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
  letI := Fintype.ofFinite (𝓞 (QNeg d) ⧸ 𝔭.asIdeal)
  rw [Int.cast_ofNat, FiniteField.isSquare_two_iff, ← Nat.card_eq_fintype_card, hq]
  rw [hq] at hodd
  have hc : ((Algebra.norm ℤ β).natAbs : ℤ) = Algebra.norm ℤ β := Int.natAbs_of_nonneg hnn
  have h8 : ((Algebra.norm ℤ β).natAbs : ℤ) % 8 = 1 := by
    have : ((Algebra.norm ℤ β).natAbs : ℤ) % 2 = 1 := by exact_mod_cast hodd
    rcases Int.emod_two_eq_zero_or_one a with ha | ha
    · obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
      rw [hc, hN] at this; ring_nf at this; omega
    · obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k + 1 := ⟨a / 2, by omega⟩
      obtain ⟨r, hr⟩ := Int.even_mul_succ_self k
      have e : (2 * k + 1) ^ 2 = 8 * r + 1 := by linear_combination 4 * hr
      rw [hc, hN, e]; omega
  omega

end SqrtTwo

end ZInQ.Contrib.TYZGenus.RingClass
