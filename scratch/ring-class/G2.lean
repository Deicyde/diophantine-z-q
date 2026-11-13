import ZInQKernel.Contrib.TYZGenus.RingClassGalois
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.Different.Derivative
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.ArtinSymbol

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory IsDedekindDomain Polynomial

noncomputable section
namespace ZInQ.Contrib.TYZGenus.RingClass

section SqrtNegOne

variable (K : Type) [Field K] [NumberField K]

/-- A square root of `−1` in `Kˢ`. -/
def jK : SeparableClosure K :=
  (IsSepClosed.exists_pow_nat_eq (k := SeparableClosure K) (-1) 2).choose

theorem jK_sq : jK K ^ 2 = -1 :=
  (IsSepClosed.exists_pow_nat_eq (k := SeparableClosure K) (-1) 2).choose_spec

theorem isIntegral_jK : IsIntegral K (jK K) :=
  ⟨X ^ 2 + 1, monic_X_pow_add_C 1 two_ne_zero, by simp [jK_sq]⟩

/-- `K(√−1) ⊆ Kˢ`. -/
abbrev adjI : IntermediateField K (SeparableClosure K) := IntermediateField.adjoin K {jK K}

instance : FiniteDimensional K (adjI K) := IntermediateField.adjoin.finiteDimensional (isIntegral_jK K)

instance : NumberField (adjI K) := NumberField.of_module_finite K (adjI K)

theorem sq_eq_neg_one_iff {F : Type*} [CommRing F] [IsDomain F] {x y : F} (hy : y ^ 2 = -1) :
    x ^ 2 = -1 ↔ x = y ∨ x = -y := by
  rw [← hy]; exact sq_eq_sq_iff_eq_or_eq_neg

instance : Normal K (adjI K) := by
  rw [IntermediateField.normal_iff_forall_map_le']
  intro g
  rw [IntermediateField.adjoin_map, Set.image_singleton, IntermediateField.adjoin_le_iff,
    Set.singleton_subset_iff]
  have h : g (jK K) ^ 2 = -1 := by rw [← map_pow, jK_sq, map_neg, map_one]
  rcases (sq_eq_neg_one_iff (jK_sq K)).1 h with h | h
  · simp only [AlgEquiv.coe_algHom, h, SetLike.mem_coe]
    exact IntermediateField.mem_adjoin_simple_self K _
  · simp only [AlgEquiv.coe_algHom, h, SetLike.mem_coe]
    exact neg_mem (IntermediateField.mem_adjoin_simple_self K _)

instance : IsGalois K (adjI K) := IsGalois.mk

theorem gen_sq : (IntermediateField.AdjoinSimple.gen K (jK K)) ^ 2 = -1 :=
  Subtype.ext (by simp [jK_sq])

/-- `√−1` as an element of `𝓞_{K(√−1)}`. -/
def jO : 𝓞 (adjI K) :=
  ⟨IntermediateField.AdjoinSimple.gen K (jK K), by
    refine ⟨X ^ 2 + 1, monic_X_pow_add_C 1 two_ne_zero, ?_⟩
    simp [gen_sq]⟩

theorem jO_sq : jO K ^ 2 = -1 := by
  apply RingOfIntegers.ext
  simp only [RingOfIntegers.coe_eq_algebraMap, map_pow, map_neg, map_one]
  exact gen_sq K

theorem adjoin_jO_eq_top :
    Algebra.adjoin K {algebraMap (𝓞 (adjI K)) (adjI K) (jO K)} = ⊤ :=
  (IntermediateField.adjoin.powerBasis (isIntegral_jK K)).adjoin_gen_eq_top

variable {K}

/-- Primes `Q` of `𝓞_{K(√−1)}` not containing `2` are unramified over `𝓞_K`. -/
theorem isUnramifiedAt_of_two_notMem (Q : Ideal (𝓞 (adjI K))) [Q.IsPrime]
    (h2 : (2 : 𝓞 (adjI K)) ∉ Q) : Algebra.IsUnramifiedAt (𝓞 K) Q := by
  refine not_dvd_differentIdeal_iff.1 fun hdvd => h2 ?_
  have hmem := TauCeti.natCast_mul_mem_differentIdeal_of_pow_eq (A := 𝓞 K) (K := K)
    (L := adjI K) (B := 𝓞 (adjI K)) (adjoin_jO_eq_top K) (n := 2) (a := -1)
    (by rw [jO_sq, map_neg, map_one])
  have := Ideal.le_of_dvd hdvd hmem
  have h' : (2 : 𝓞 (adjI K)) = -(((2 : ℕ) : 𝓞 (adjI K)) * algebraMap (𝓞 K) (𝓞 (adjI K)) (-1)) := by
    simp
  rw [h']
  exact Q.neg_mem_iff.2 this

/-- **An arithmetic Frobenius at a prime of residue norm `≡ 1 (mod 4)` prime to `2` is trivial on
`K(√−1)`.** -/
theorem eq_one_of_isArithFrobAt (Q : Ideal (𝓞 (adjI K))) [Q.IsPrime]
    (h2 : (2 : 𝓞 (adjI K)) ∉ Q) (σ : adjI K ≃ₐ[K] adjI K) (hσ : IsArithFrobAt (𝓞 K) σ Q)
    (hq : Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) % 4 = 1) : σ = 1 := by
  have h := hσ (jO K)
  simp only [MulSemiringAction.toAlgHom_apply] at h
  obtain ⟨k, hk⟩ : ∃ k, Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) = 4 * k + 1 := ⟨Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) / 4, by omega⟩
  have hpow : jO K ^ Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) = jO K := by
    rw [hk, pow_succ, pow_mul, show jO K ^ 4 = (jO K ^ 2) ^ 2 by ring, jO_sq]
    simp
  rw [hpow] at h
  have hsq : (σ • jO K) ^ 2 = -1 := by
    rw [← smul_pow', jO_sq, smul_neg, smul_one]
  have hfix : σ • jO K = jO K := by
    rcases (sq_eq_neg_one_iff (jO_sq K)).1 hsq with h1 | h1
    · exact h1
    · exfalso
      apply h2
      rw [h1] at h
      have : (-jO K - jO K) * jO K ∈ Q := Q.mul_mem_right _ h
      have e : (-jO K - jO K) * jO K = 2 := by
        have := jO_sq K
        linear_combination (-2 : 𝓞 (adjI K)) * this
      rwa [e] at this
  have hfix' : σ (IntermediateField.AdjoinSimple.gen K (jK K)) =
      IntermediateField.AdjoinSimple.gen K (jK K) := congrArg Subtype.val hfix
  apply AlgEquiv.coe_algHom_injective
  apply IntermediateField.adjoin_algHom_ext
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact hfix'

/-- **Primes of residue norm `≡ 1 (mod 4)` prime to `2` split completely in `K(√−1)`.** -/
theorem mem_splitSet_adjI (𝔭 : HeightOneSpectrum (𝓞 K)) (h2 : (2 : 𝓞 K) ∉ 𝔭.asIdeal)
    (hq : Nat.card (𝓞 K ⧸ 𝔭.asIdeal) % 4 = 1) : 𝔭 ∈ splitSet K (adjI K) := by
  have h2Q : ∀ (Q : Ideal (𝓞 (adjI K))) [Q.LiesOver 𝔭.asIdeal], (2 : 𝓞 (adjI K)) ∉ Q := by
    intro Q _ h
    apply h2
    have : algebraMap (𝓞 K) (𝓞 (adjI K)) 2 ∈ Q := by rwa [map_ofNat]
    rwa [← Ideal.mem_comap, ← Ideal.under_def, ← Ideal.over_def Q 𝔭.asIdeal] at this
  have hur : ∀ (Q : Ideal (𝓞 (adjI K))) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q := fun Q _ _ => isUnramifiedAt_of_two_notMem Q (h2Q Q)
  obtain ⟨Q, hQp, hQo⟩ := (inferInstance : Nonempty (𝔭.asIdeal.primesOver (𝓞 (adjI K))))
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt K Q hQ
  have hσ1 : σ = 1 :=
    eq_one_of_isArithFrobAt Q (h2Q Q) σ hσ (by rwa [← Ideal.over_def Q 𝔭.asIdeal])
  have hA := artinSymbol_eq_mk_of_isArithFrobAt 𝔭.asIdeal hur Q σ hσ
  rw [hσ1, ← ConjClasses.one_eq_mk_one] at hA
  exact (artinSymbol_eq_one_iff_ncard_primesOver_eq_finrank 𝔭.asIdeal hur).1 hA

/-- The residue field of a prime not containing `2` has odd cardinality. -/
theorem card_quot_odd (𝔭 : HeightOneSpectrum (𝓞 K)) (h2 : (2 : 𝓞 K) ∉ 𝔭.asIdeal) :
    Nat.card (𝓞 K ⧸ 𝔭.asIdeal) % 2 = 1 := by
  letI := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
  letI := Fintype.ofFinite (𝓞 K ⧸ 𝔭.asIdeal)
  rw [Nat.card_eq_fintype_card]
  refine FiniteField.odd_card_of_char_ne_two fun hc => h2 ?_
  have : ((2 : ℕ) : 𝓞 K ⧸ 𝔭.asIdeal) = 0 := by
    rw [← hc]; exact ringChar.Nat.cast_ringChar
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
  simpa using this

end SqrtNegOne

section IInH4

open ZInQ.RouteK.Rank5b ZInQ.RouteK.Redei ZInQ.Contrib.TYZDecomp.CurveA

variable {d : ℕ} [NeZero d]

/-- Norms of elements of `O_{d,4} = ℤ + 4𝓞_K` are `≡ a² (mod 4)`. -/
theorem norm_of_mem_O4 (β : 𝓞 (QNeg d)) (hβ : β ∈ (O4 d).toRingOfIntegers) :
    ∃ a c : ℤ, Algebra.norm ℤ β = a ^ 2 + 4 * c := by
  obtain ⟨a, y, hy⟩ := (NumberFieldOrder.mem_toRingOfIntegers _).1 hβ
  obtain ⟨m, hm⟩ := exists_two_re y
  refine ⟨a, a * m + 4 * Algebra.norm ℤ y, ?_⟩
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
  have : ((Algebra.norm ℤ β : ℤ) : ℚ) = ((a ^ 2 + 4 * (a * m + 4 * Algebra.norm ℤ y) : ℤ) : ℚ) := by
    push_cast
    rw [h1, h2, ← hm]
    ring
  exact_mod_cast this

theorem finite_two_conductor_primes :
    {𝔭 : HeightOneSpectrum (𝓞 (QNeg d)) |
      (O4 d).conductor * Ideal.span {2} ≤ 𝔭.asIdeal}.Finite := by
  have hne : (O4 d).conductor * Ideal.span {(2 : 𝓞 (QNeg d))} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.mul_eq_bot, not_or]
    refine ⟨by simpa using (O4 d).conductor_ne_bot, ?_⟩
    rw [Ideal.span_singleton_eq_bot]
    exact two_ne_zero
  refine (Ideal.finite_factors hne).subset fun 𝔭 h𝔭 => ?_
  exact Ideal.dvd_iff_le.2 h𝔭

/-- **`K_d(√−1) ⊆ H_{d,4}`** (genus theory of the order `ℤ + 4𝓞_K`), via Bauer's theorem: a prime
`𝔭 ∤ 2` splitting completely in `H_{d,4}` is `β𝓞_K` with `β ∈ ℤ + 4𝓞_K`, so `N𝔭 ≡ 1 (mod 4)` and
`𝔭` splits completely in `K_d(√−1)`. -/
theorem adjI_le_H4 : adjI (QNeg d) ≤ H4 d := by
  rw [H4_eq_ringSubfield]
  refine le_of_splitSet_diff_subset _ finite_two_conductor_primes ?_
  rintro 𝔭 ⟨h𝔭, hT⟩
  have hT1 : ¬ (O4 d).conductor ≤ 𝔭.asIdeal := fun h => hT (le_trans Ideal.mul_le_left h)
  have h2 : (2 : 𝓞 (QNeg d)) ∉ 𝔭.asIdeal := fun h =>
    hT (le_trans Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h))
  have hJ := mem_primeTo_of_not_le 𝔭 hT1
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
    Ideal (𝓞 (QNeg d))).IsMaximal := 𝔭.isMaximal
  have h1 := (mem_splitSet_iff (O4 d) ⊥ ⟨_, hJ⟩ 𝔭 rfl).1 h𝔭
  rw [Subgroup.mem_bot, picClass_eq_one_iff] at h1
  obtain ⟨β, hβ, hspan⟩ := h1
  obtain ⟨a, c, hN⟩ := norm_of_mem_O4 β hβ
  have hq : Nat.card (𝓞 (QNeg d) ⧸ 𝔭.asIdeal) = (Algebra.norm ℤ β).natAbs := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    change Ideal.absNorm (((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
      Ideal (𝓞 (QNeg d)))) = _
    rw [hspan, Ideal.absNorm_span_singleton]
  have hodd := card_quot_odd 𝔭 h2
  have hnn := normZ_nonneg (n := d) β
  refine mem_splitSet_adjI 𝔭 h2 ?_
  rw [hq] at hodd ⊢
  have hc : ((Algebra.norm ℤ β).natAbs : ℤ) = Algebra.norm ℤ β := Int.natAbs_of_nonneg hnn
  have h4 : ((Algebra.norm ℤ β).natAbs : ℤ) % 4 = 1 := by
    rw [hc, hN]
    have : ((Algebra.norm ℤ β).natAbs : ℤ) % 2 = 1 := by exact_mod_cast hodd
    rw [hc, hN] at this
    rcases Int.emod_two_eq_zero_or_one a with ha | ha <;>
    · obtain ⟨k, hk⟩ : ∃ k, a = 2 * k + a % 2 := ⟨a / 2, by omega⟩
      rw [ha] at hk
      subst hk
      ring_nf at this ⊢
      omega
  omega

/-- **`i ∈ H_{d,4}`** for every `d ≥ 1`: some square root of `−1` of `K_dˢ` lies in `H_{d,4}`. -/
theorem jK_mem_H4 : jK (QNeg d) ∈ H4 d :=
  adjI_le_H4 (IntermediateField.mem_adjoin_simple_self _ _)

omit [NeZero d] in
/-- **`i ∈ H_{d,4} ⊂ ℚ̄`** for every `d ≥ 1`. -/
theorem iQ_mem_H4bar (hd : d ≠ 0) : iQ ∈ H4bar d := by
  have : NeZero d := ⟨hd⟩
  rw [H4bar_eq_map]
  have hmem : embed d (jK (QNeg d)) ∈ ((H4 d).restrictScalars ℚ).map (embed d) :=
    ⟨jK (QNeg d), jK_mem_H4, rfl⟩
  have hsq : (embed d (jK (QNeg d))) ^ 2 = -1 := by
    rw [← map_pow, jK_sq, map_neg, map_one]
  rcases (sq_eq_neg_one_iff hsq).1 iQ_sq with h | h
  · rw [h]; exact hmem
  · rw [h]; exact neg_mem hmem

end IInH4

end ZInQ.Contrib.TYZGenus.RingClass
