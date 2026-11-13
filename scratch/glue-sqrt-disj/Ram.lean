import Mathlib

open Polynomial IsLocalRing

namespace GlueSqrtDisj

variable (p : ℕ) [hp : Fact p.Prime] (L : Type) [Field L] [Algebra ℚ_[p] L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]

/-- `ℤ_p/(p)` has `p` elements (copied from glue-sqrt-local). -/
theorem card_quotient_maximalIdeal : Nat.card (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) = p := by
  rw [← PadicInt.ker_toZMod]
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (ZMod.ringHom_surjective (PadicInt.toZMod (p := p)))).toEquiv]
  simp

/-- Two `m`-th roots of unity congruent modulo a prime `Q` with `m ∉ Q` are equal
(copied from glue-sqrt-local). -/
theorem eq_of_pow_eq_one_of_sub_mem {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) {m : ℕ}
    {x y : R} (hx : x ^ m = 1) (hy : y ^ m = 1) (hxy : x - y ∈ Q) (hm : (m : R) ∉ Q) :
    x = y := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  by_contra hne
  have h1 : (∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)) = 0 := by
    have := geom_sum₂_mul x y m
    rw [hx, hy, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  have h2 : Ideal.Quotient.mk Q x = Ideal.Quotient.mk Q y := Ideal.Quotient.eq.mpr hxy
  have h3 := congrArg (Ideal.Quotient.mk Q) h1
  simp only [map_sum, map_mul, map_pow, h2, map_zero] at h3
  have h4 : ∀ i ∈ Finset.range m, (Ideal.Quotient.mk Q y) ^ i * (Ideal.Quotient.mk Q y) ^ (m - 1 - i)
      = (Ideal.Quotient.mk Q y) ^ (m - 1) := fun i hi => by
    rw [← pow_add]; congr 1; have := Finset.mem_range.mp hi; omega
  rw [Finset.sum_congr rfl h4, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h3
  have h5 : (Ideal.Quotient.mk Q y) ^ (m - 1) * Ideal.Quotient.mk Q y = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0), ← map_pow, hy, map_one]
  have h6 : (m : R ⧸ Q) = 0 := by
    have := congrArg (· * Ideal.Quotient.mk Q y) h3
    simp only [zero_mul, mul_assoc, h5, mul_one] at this
    exact this
  apply hm
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h6

/-- In a domain, if `p` lies in a prime `Q` and `z` is a primitive `p^k`-th root of unity, then
`p ∈ Q^φ(p^k)`: `p = Φ_{p^k}(1) = ∏ (1 - μ)` over the primitive roots `μ`, and each `1 - μ`
lies in `Q`. -/
theorem prime_mem_pow_totient {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) [Q.IsPrime]
    {k : ℕ} {z : R} (hz : IsPrimitiveRoot z (p ^ k)) (hpQ : (p : R) ∈ Q) :
    (p : R) ∈ Q ^ (p ^ k).totient := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hpQ
  have hpk : 0 < p ^ k := pow_pos hp.out.pos k
  have hprod : (p : R) = ∏ μ ∈ primitiveRoots (p ^ k) R, (1 - μ) := by
    have h1 := congrArg (eval 1) (cyclotomic_eq_prod_X_sub_primitiveRoots hz)
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [eval_one_cyclotomic_prime_pow (R := R) (p := p) j, eval_prod] at h1
    simpa using h1
  -- some `1 - μ₀` lies in `Q`
  obtain ⟨μ₀, hμ₀, hμ₀Q⟩ : ∃ μ₀ ∈ primitiveRoots (p ^ k) R, 1 - μ₀ ∈ Q := by
    rw [hprod] at hpQ
    exact (Ideal.IsPrime.prod_mem_iff (p := Q)).mp hpQ
  have hμ₀' : IsPrimitiveRoot μ₀ (p ^ k) := (mem_primitiveRoots hpk).mp hμ₀
  have hall : ∀ μ ∈ primitiveRoots (p ^ k) R, 1 - μ ∈ Q := by
    intro μ hμ
    have hμ' : IsPrimitiveRoot μ (p ^ k) := (mem_primitiveRoots hpk).mp hμ
    obtain ⟨i, -, rfl⟩ := hμ₀'.eq_pow_of_pow_eq_one hμ'.pow_eq_one
    obtain ⟨c, hc⟩ := one_sub_dvd_one_sub_pow μ₀ i
    rw [hc]
    exact Q.mul_mem_right c hμ₀Q
  have := Ideal.prod_mem_prod (s := primitiveRoots (p ^ k) R) (I := fun _ => Q)
    (x := fun μ => 1 - μ) hall
  rw [Finset.prod_const, hz.card_primitiveRoots] at this
  rw [hprod]
  exact this


/-- **Degree bound.** Let `L/ℚ_p` be finite Galois, containing a primitive `p^k`-th root of
unity `ζ` and a primitive `m`-th root of unity `η` with `p ∤ m`. Then
`φ(p^k) · ord_m(p) ≤ [L:ℚ_p]`. Proof: the fundamental identity `g·e·f = |Gal(L/ℚ_p)|` for the
integral closure `S` of `ℤ_p`; `e ≥ φ(p^k)` because `p ∈ Q^φ(p^k)`; `f ≥ ord_m(p)` because
`η^(p^f) = η` (Frobenius of `S/Q`, and `m`-th roots of unity stay distinct mod `Q`). -/
theorem totient_mul_orderOf_le_finrank {k m : ℕ} [NeZero m] (hcop : p.Coprime m) {ζ η : L}
    (hζ : IsPrimitiveRoot ζ (p ^ k)) (hη : IsPrimitiveRoot η m) :
    (p ^ k).totient * orderOf (ZMod.unitOfCoprime p hcop) ≤ Module.finrank ℚ_[p] L := by
  let S := integralClosure ℤ_[p] L
  have : IsFractionRing S L := integralClosure.isFractionRing_of_finite_extension ℚ_[p] L
  have : IsGaloisGroup Gal(L/ℚ_[p]) ℤ_[p] S :=
    IsGaloisGroup.of_isFractionRing Gal(L/ℚ_[p]) ℤ_[p] S ℚ_[p] L
  have : Module.Finite ℤ_[p] S := IsIntegralClosure.finite ℤ_[p] ℚ_[p] L S
  have hinjL : Function.Injective (algebraMap ℤ_[p] L) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] L]
    exact (algebraMap ℚ_[p] L).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])
  have : FaithfulSMul ℤ_[p] S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply hinjL
    rw [IsScalarTower.algebraMap_apply ℤ_[p] S L, h, ← IsScalarTower.algebraMap_apply]
  have : IsDedekindDomain S := integralClosure.isDedekindDomain ℤ_[p] ℚ_[p] L
  have : Module.Flat ℤ_[p] S := inferInstance
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := S)
    (maximalIdeal ℤ_[p])
  have hunder : Q.under ℤ_[p] = maximalIdeal ℤ_[p] := (Ideal.liesOver_iff _ _).mp hQ |>.symm
  -- the fundamental identity
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (maximalIdeal ℤ_[p]) S Gal(L/ℚ_[p])
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal ℤ_[p]) Q Gal(L/ℚ_[p]),
    Ideal.inertiaDegIn_eq_inertiaDeg (maximalIdeal ℤ_[p]) Q Gal(L/ℚ_[p]),
    IsGalois.card_aut_eq_finrank] at hfund
  have hG : 0 < Module.finrank ℚ_[p] L := Module.finrank_pos
  have hef : Q.ramificationIdx ℤ_[p] * Q.inertiaDeg ℤ_[p] ≤ Module.finrank ℚ_[p] L := by
    rw [← hfund]
    apply Nat.le_mul_of_pos_left
    rcases Nat.eq_zero_or_pos (Ideal.primesOver (maximalIdeal ℤ_[p]) S).ncard with h | h
    · rw [h, zero_mul] at hfund; omega
    · exact h
  refine le_trans (Nat.mul_le_mul ?_ ?_) hef
  · -- `e ≥ φ(p^k)`
    have hpQ : (p : S) ∈ Q := by
      have : (p : ℤ_[p]) ∈ Q.under ℤ_[p] := by
        rw [hunder, PadicInt.maximalIdeal_eq_span_p]
        exact Ideal.subset_span rfl
      rw [Ideal.under, Ideal.mem_comap, map_natCast] at this
      exact this
    have hζS : IsIntegral ℤ_[p] ζ := ⟨X ^ (p ^ k) - C 1,
      monic_X_pow_sub_C 1 (pow_pos hp.out.pos k).ne', by simp [hζ.pow_eq_one]⟩
    let z : S := ⟨ζ, hζS⟩
    have hz : IsPrimitiveRoot z (p ^ k) :=
      IsPrimitiveRoot.of_map_of_injective (f := (integralClosure ℤ_[p] L).val) hζ
        Subtype.val_injective
    have hmem := prime_mem_pow_totient p Q hz hpQ
    have hne : Ideal.map (algebraMap ℤ_[p] S) (maximalIdeal ℤ_[p]) ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot (by
        rw [PadicInt.maximalIdeal_eq_span_p]; simp [hp.out.ne_zero])
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (maximalIdeal ℤ_[p]) Q hne]
    have hQ0 : ¬ IsUnit Q := by
      rw [Ideal.isUnit_iff]; exact hQmax.ne_top
    apply (FiniteMultiplicity.of_not_isUnit hQ0 hne).le_multiplicity_of_pow_dvd
    rw [Ideal.dvd_iff_le, PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton,
      Ideal.span_le, Set.singleton_subset_iff, map_natCast]
    exact hmem
  · -- `f ≥ ord_m(p)`
    have hm : ¬ p ∣ m := (Nat.Prime.coprime_iff_not_dvd hp.out).mp hcop
    have hm0 : m ≠ 0 := NeZero.ne m
    have hcard := Ideal.cardQuot_pow_inertiaDeg (maximalIdeal ℤ_[p]) Q
    rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hcard
    change Nat.card (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) ^ _ = Nat.card (S ⧸ Q) at hcard
    rw [card_quotient_maximalIdeal p] at hcard
    set f := Q.inertiaDeg ℤ_[p]
    have hf : 0 < f := Ideal.inertiaDeg_pos (R := ℤ_[p]) Q
    let _ : Field (S ⧸ Q) := Ideal.Quotient.field Q
    have : Finite (S ⧸ Q) := Nat.finite_of_card_ne_zero (by
      rw [← hcard]; exact pow_ne_zero _ hp.out.ne_zero)
    let _ := Fintype.ofFinite (S ⧸ Q)
    have hηS : IsIntegral ℤ_[p] η := ⟨X ^ m - C 1, monic_X_pow_sub_C 1 hm0,
      by simp [hη.pow_eq_one]⟩
    let w : S := ⟨η, hηS⟩
    have hw : w ^ m = 1 := Subtype.ext (by simp [w, hη.pow_eq_one])
    have hmQ : (m : S) ∉ Q := by
      intro h
      have h1 : (m : ℤ_[p]) ∈ Q.under ℤ_[p] := by
        rw [Ideal.under, Ideal.mem_comap, map_natCast]; exact h
      rw [hunder, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast,
        ZMod.natCast_eq_zero_iff] at h1
      exact hm h1
    have hfrob : Ideal.Quotient.mk Q (w ^ (p ^ f)) = Ideal.Quotient.mk Q w := by
      rw [map_pow, hcard, Nat.card_eq_fintype_card, FiniteField.pow_card]
    have hwf : w ^ (p ^ f) = w := by
      refine eq_of_pow_eq_one_of_sub_mem Q (m := m) ?_ hw (Ideal.Quotient.eq.mp hfrob) hmQ
      rw [← pow_mul, mul_comm, pow_mul, hw, one_pow]
    have hηf : η ^ (p ^ f) = η := by
      have := congrArg Subtype.val hwf
      simpa [w] using this
    have hpf : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.out.pos
    have h1 : η ^ (p ^ f - 1) = 1 := by
      apply mul_right_cancel₀ (hη.ne_zero hm0)
      rw [← pow_succ, Nat.sub_add_cancel hpf, one_mul]; exact hηf
    have h2 : m ∣ p ^ f - 1 := hη.dvd_of_pow_eq_one _ h1
    have h3 : ((p ^ f - 1 : ℕ) : ZMod m) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h2
    rw [Nat.cast_sub hpf, sub_eq_zero, Nat.cast_pow, Nat.cast_one] at h3
    apply orderOf_le_of_pow_eq_one hf
    ext
    simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one]
    exact h3

end GlueSqrtDisj

#print axioms GlueSqrtDisj.totient_mul_orderOf_le_finrank
