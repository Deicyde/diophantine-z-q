import Mathlib

open Polynomial IsLocalRing
open scoped Pointwise

namespace GlueSqrtLocal

variable (p : ℕ) [hp : Fact p.Prime] (L : Type) [Field L] [Algebra ℚ_[p] L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]

/-! ### Locality of the integral closure (spectral norm) -/

/-- `y ∈ L` is integral over `ℤ_p` iff its spectral norm is at most `1`. -/
theorem isIntegral_iff_spectralNorm_le_one (y : L) :
    IsIntegral ℤ_[p] y ↔ spectralNorm ℚ_[p] L y ≤ 1 := by
  have hyQ : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hyQ)]
  constructor
  · intro hy n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hy, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl : minpoly ℚ_[p] y ∈ lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyQ)
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[p], hq, minpoly.aeval]

local notation "N" => spectralNorm ℚ_[p] L

theorem spectralNorm_mul' (x y : L) : N (x * y) = N x * N y :=
  (spectralMulAlgNorm ℚ_[p] L).map_mul x y

/-- **The integral closure of `ℤ_p` in a finite extension `L` of `ℚ_p` is a local ring.** -/
theorem isLocalRing_integralClosure : IsLocalRing (integralClosure ℤ_[p] L) := by
  have hle : ∀ x : integralClosure ℤ_[p] L, N (x : L) ≤ 1 := fun x =>
    (isIntegral_iff_spectralNorm_le_one p L x).mp x.2
  have hunit : ∀ x : integralClosure ℤ_[p] L, IsUnit x ↔ N (x : L) = 1 := by
    intro x
    constructor
    · rintro ⟨u, rfl⟩
      have h1 : N ((u : integralClosure ℤ_[p] L) : L) * N (((u⁻¹ : _ˣ) : integralClosure ℤ_[p] L) : L)
          = 1 := by
        rw [← spectralNorm_mul', ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one,
          spectralNorm_one]
      have a1 := hle u
      have a2 := hle (u⁻¹ : _ˣ)
      have b1 := spectralNorm_nonneg (K := ℚ_[p]) ((u : integralClosure ℤ_[p] L) : L)
      have b2 := spectralNorm_nonneg (K := ℚ_[p]) (((u⁻¹ : _ˣ) : integralClosure ℤ_[p] L) : L)
      nlinarith
    · intro h
      have hx0 : (x : L) ≠ 0 := by
        intro h0; rw [h0, spectralNorm_zero] at h; exact zero_ne_one h
      have hinv : N ((x : L)⁻¹) = 1 := by
        have := spectralNorm_mul' p L (x : L) (x : L)⁻¹
        rw [mul_inv_cancel₀ hx0, spectralNorm_one, h, one_mul] at this
        exact this.symm
      have hint : IsIntegral ℤ_[p] ((x : L)⁻¹) :=
        (isIntegral_iff_spectralNorm_le_one p L _).mpr hinv.le
      refine IsUnit.of_mul_eq_one (⟨_, hint⟩ : integralClosure ℤ_[p] L) ?_
      apply Subtype.ext
      simp [hx0]
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [mem_nonunits_iff, hunit] at ha hb ⊢
  have ha' : N (a : L) < 1 := lt_of_le_of_ne (hle a) ha
  have hb' : N (b : L) < 1 := lt_of_le_of_ne (hle b) hb
  have := isNonarchimedean_spectralNorm (K := ℚ_[p]) (L := L) (a : L) (b : L)
  rw [Subalgebra.coe_add]
  intro hab
  rw [hab] at this
  exact absurd this (not_le.mpr (max_lt ha' hb'))


/-- `ℤ_p/(p)` has `p` elements. -/
theorem card_quotient_maximalIdeal : Nat.card (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) = p := by
  rw [← PadicInt.ker_toZMod]
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (ZMod.ringHom_surjective (PadicInt.toZMod (p := p)))).toEquiv]
  simp

/-- **Frobenius in a finite Galois extension of `ℚ_p`.** There is `σ ∈ Gal(L/ℚ_p)` with
`σ ζ = ζ^p` for every root of unity `ζ ∈ L` of order prime to `p`. -/
theorem exists_frobenius :
    ∃ σ : Gal(L/ℚ_[p]), ∀ (m : ℕ), ¬ p ∣ m → ∀ ζ : L, ζ ^ m = 1 → σ ζ = ζ ^ p := by
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
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := S)
    (maximalIdeal ℤ_[p])
  have hunder : Q.under ℤ_[p] = maximalIdeal ℤ_[p] := (Ideal.liesOver_iff _ _).mp hQ |>.symm
  have : Finite (ℤ_[p] ⧸ Q.under ℤ_[p]) := by
    rw [hunder]
    exact Nat.finite_of_card_ne_zero (by rw [card_quotient_maximalIdeal p]; exact hp.out.ne_zero)
  have : Module.Finite (ℤ_[p] ⧸ Q.under ℤ_[p]) (S ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite ℤ_[p] _ _
  have : Finite (S ⧸ Q) := Module.finite_of_finite (ℤ_[p] ⧸ Q.under ℤ_[p])
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ_[p] Gal(L/ℚ_[p]) Q
  refine ⟨σ, fun m hm ζ hζ => ?_⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hζS : IsIntegral ℤ_[p] ζ := ⟨X ^ m - C 1, monic_X_pow_sub_C 1 hm0, by simp [hζ]⟩
  let z : S := ⟨ζ, hζS⟩
  have hz : z ^ m = 1 := Subtype.ext (by simp [z, hζ])
  have hmQ : (m : S) ∉ Q := by
    intro h
    have h1 : (m : ℤ_[p]) ∈ Q.under ℤ_[p] := by
      rw [Ideal.under, Ideal.mem_comap, map_natCast]; exact h
    rw [hunder, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast,
      ZMod.natCast_eq_zero_iff] at h1
    exact hm h1
  have key := hσ.apply_of_pow_eq_one hz hmQ
  rw [hunder, card_quotient_maximalIdeal p] at key
  have := congrArg (fun s : S => (s : L)) key
  simp only [SubmonoidClass.coe_pow, z] at this
  exact this

/-- Two `m`-th roots of unity congruent modulo a prime `Q` with `m ∉ Q` are equal. -/
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

attribute [local instance] Ideal.Quotient.field in
/-- **Every element of `Gal(L/ℚ_p)` acts as a power of Frobenius on prime-to-`p` roots of
unity**, provided the integral closure of `ℤ_p` in `L` is local (true for every finite `L/ℚ_p`;
not proved here). -/
theorem pow_frobenius_of_isLocalRing (hloc : IsLocalRing (integralClosure ℤ_[p] L))
    (τ : Gal(L/ℚ_[p])) :
    ∃ n : ℕ, ∀ m : ℕ, ¬ p ∣ m → ∀ ζ : L, ζ ^ m = 1 → τ ζ = ζ ^ (p ^ n) := by
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
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := S)
    (maximalIdeal ℤ_[p])
  have hunder : Q.under ℤ_[p] = maximalIdeal ℤ_[p] := (Ideal.liesOver_iff _ _).mp hQ |>.symm
  have : Finite (ℤ_[p] ⧸ Q.under ℤ_[p]) := by
    rw [hunder]
    exact Nat.finite_of_card_ne_zero (by rw [card_quotient_maximalIdeal p]; exact hp.out.ne_zero)
  have : Module.Finite (ℤ_[p] ⧸ Q.under ℤ_[p]) (S ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite ℤ_[p] _ _
  have : Finite (S ⧸ Q) := Module.finite_of_finite (ℤ_[p] ⧸ Q.under ℤ_[p])
  have hQeq : Q = maximalIdeal S := IsLocalRing.eq_maximalIdeal hQmax
  have hstab : τ ∈ MulAction.stabilizer Gal(L/ℚ_[p]) Q := by
    rw [MulAction.mem_stabilizer_iff, hQeq]
    ext x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, IsLocalRing.mem_maximalIdeal,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
    exact isUnit_map_iff (MulSemiringAction.toRingEquiv Gal(L/ℚ_[p]) S τ⁻¹) x
  have : (Q.under ℤ_[p]).IsMaximal := by rw [hunder]; infer_instance
  let φ := Ideal.Quotient.stabilizerHom Q (Q.under ℤ_[p]) Gal(L/ℚ_[p]) ⟨τ, hstab⟩
  have : Fintype (ℤ_[p] ⧸ Q.under ℤ_[p]) := Fintype.ofFinite _
  obtain ⟨⟨n, _hnlt⟩, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
    (ℤ_[p] ⧸ Q.under ℤ_[p]) (S ⧸ Q)).2 φ
  have hcard : Fintype.card (ℤ_[p] ⧸ Q.under ℤ_[p]) = p := by
    rw [Fintype.card_eq_nat_card, Nat.card_congr (Ideal.quotEquivOfEq hunder).toEquiv,
      card_quotient_maximalIdeal p]
  refine ⟨n, fun m hm ζ hζ => ?_⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hζS : IsIntegral ℤ_[p] ζ := ⟨X ^ m - C 1, monic_X_pow_sub_C 1 hm0, by simp [hζ]⟩
  let z : S := ⟨ζ, hζS⟩
  have hz : z ^ m = 1 := Subtype.ext (by simp [z, hζ])
  have hmQ : (m : S) ∉ Q := by
    intro h
    have h1 : (m : ℤ_[p]) ∈ Q.under ℤ_[p] := by
      rw [Ideal.under, Ideal.mem_comap, map_natCast]; exact h
    rw [hunder, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast,
      ZMod.natCast_eq_zero_iff] at h1
    exact hm h1
  have h1 : Ideal.Quotient.mk Q (τ • z) = Ideal.Quotient.mk Q (z ^ (p ^ n)) := by
    have := congrArg (fun f => f (Ideal.Quotient.mk Q z)) hn
    simp only at this
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, hcard] at this
    beta_reduce at this
    rw [map_pow, this]
    rfl
  have hτz : (τ • z) ^ m = 1 := by rw [← smul_pow', hz, smul_one]
  have hzp : (z ^ (p ^ n)) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
  have h2 := eq_of_pow_eq_one_of_sub_mem Q hτz hzp (Ideal.Quotient.eq.mp h1) hmQ
  have := congrArg (fun s : S => (s : L)) h2
  simp only [SubmonoidClass.coe_pow, z] at this
  exact this

/-- If `σ ζ = ζ^k` for a primitive `m`-th root `ζ`, then `autToPow σ = k` in `ZMod m`. -/
theorem autToPow_eq_of_apply {K F : Type*} [Field K] [Field F] [Algebra K F] {m : ℕ} [NeZero m]
    {ζ : F} (hζ : IsPrimitiveRoot ζ m) (σ : Gal(F/K)) (k : ℕ) (h : σ ζ = ζ ^ k) :
    ((hζ.autToPow K σ : (ZMod m)ˣ) : ZMod m) = k := by
  have h1 := hζ.autToPow_spec K σ
  rw [h] at h1
  have hk : ζ ^ k = ζ ^ (k % m) := by
    conv_lhs => rw [← Nat.mod_add_div k m]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  rw [hk] at h1
  have h2 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (NeZero.pos m)) h1
  rw [← ZMod.natCast_zmod_val ((hζ.autToPow K σ : (ZMod m)ˣ) : ZMod m), h2, ZMod.natCast_mod]

/-- **The unramified Galois group.** For `p ∤ m` and an `m`-th cyclotomic extension `L` of `ℚ_p`,
the image of `Gal(L/ℚ_p) ↪ (ℤ/m)ˣ` (`σ ζ = ζ^a`) is the cyclic group generated by `p`, provided the
integral closure of `ℤ_p` in `L` is local. -/
theorem range_autToPow_eq_zpowers (hloc : IsLocalRing (integralClosure ℤ_[p] L)) {m : ℕ}
    [NeZero m] (hm : ¬ p ∣ m) {ζ : L} (hζ : IsPrimitiveRoot ζ m) :
    (hζ.autToPow ℚ_[p]).range =
      Subgroup.zpowers (ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)) := by
  set u := ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)
  apply le_antisymm
  · rintro _ ⟨τ, rfl⟩
    obtain ⟨n, hn⟩ := pow_frobenius_of_isLocalRing p L hloc τ
    refine ⟨n, ?_⟩
    ext
    rw [autToPow_eq_of_apply hζ τ (p ^ n) (hn m hm ζ hζ.pow_eq_one)]
    simp [u]
  · rw [Subgroup.zpowers_le]
    obtain ⟨σ, hσ⟩ := exists_frobenius p L
    refine ⟨σ, ?_⟩
    ext
    rw [autToPow_eq_of_apply hζ σ p (hσ m hm ζ hζ.pow_eq_one)]
    simp [u]

/-- **The unramified Galois group, unconditionally.** For `p ∤ m` and a primitive `m`-th root of
unity `ζ` in a finite Galois extension `L/ℚ_p`, the image of `Gal(L/ℚ_p) → (ℤ/m)ˣ` is `⟨p⟩`. -/
theorem range_autToPow_eq_zpowers' {m : ℕ} [NeZero m] (hm : ¬ p ∣ m) {ζ : L}
    (hζ : IsPrimitiveRoot ζ m) :
    (hζ.autToPow ℚ_[p]).range =
      Subgroup.zpowers (ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)) :=
  range_autToPow_eq_zpowers p L (isLocalRing_integralClosure p L) hm hζ

/-- Every element of `Gal(L/ℚ_p)` acts as a power of Frobenius on prime-to-`p` roots of unity. -/
theorem pow_frobenius (τ : Gal(L/ℚ_[p])) :
    ∃ n : ℕ, ∀ m : ℕ, ¬ p ∣ m → ∀ ζ : L, ζ ^ m = 1 → τ ζ = ζ ^ (p ^ n) :=
  pow_frobenius_of_isLocalRing p L (isLocalRing_integralClosure p L) τ

/-- **Degree of the unramified cyclotomic extension.** If `p ∤ m` and `L` is an `m`-th cyclotomic
extension of `ℚ_p`, then `[L : ℚ_p] = ord_m(p)`, and `Gal(L/ℚ_p) ≃* ⟨p⟩ ⊆ (ℤ/m)ˣ`. -/
theorem finrank_eq_orderOf {m : ℕ} [NeZero m] (hm : ¬ p ∣ m)
    [IsCyclotomicExtension {m} ℚ_[p] L] :
    Module.finrank ℚ_[p] L =
      orderOf (ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)) := by
  have hζ := IsCyclotomicExtension.zeta_spec m ℚ_[p] L
  rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_zpowers, ← range_autToPow_eq_zpowers' p L hm hζ]
  exact (Nat.card_congr (Equiv.ofInjective _ (hζ.autToPow_injective ℚ_[p])))

/-- `Gal(L/ℚ_p)` is cyclic for an `m`-th cyclotomic extension with `p ∤ m`. -/
theorem isCyclic_gal {m : ℕ} [NeZero m] (hm : ¬ p ∣ m) [IsCyclotomicExtension {m} ℚ_[p] L] :
    IsCyclic Gal(L/ℚ_[p]) := by
  have hζ := IsCyclotomicExtension.zeta_spec m ℚ_[p] L
  have e := MonoidHom.ofInjective (hζ.autToPow_injective ℚ_[p])
  rw [range_autToPow_eq_zpowers' p L hm hζ] at e
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

end GlueSqrtLocal

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


/-! ### Disjointness: `Gal(ℚ_p(μ_{p^k m})/ℚ_p) ≅ (ℤ/p^k)ˣ × ⟨p⟩` -/

section Disj

theorem card_subgroup_prod {G N : Type*} [Group G] [Group N] (H : Subgroup G) (K : Subgroup N) :
    Nat.card (H.prod K) = Nat.card H * Nat.card K := by
  rw [Nat.card_congr (Subgroup.prodEquiv H K).toEquiv, Nat.card_prod]

open GlueSqrtLocal

variable {p L} (k m : ℕ) [NeZero m] (hcop : p.Coprime m) [IsCyclotomicExtension {p ^ k * m} ℚ_[p] L]

include hp in
theorem zeta_pow_m :
    IsPrimitiveRoot ((IsCyclotomicExtension.zeta (p ^ k * m) ℚ_[p] L) ^ m) (p ^ k) :=
  (IsCyclotomicExtension.zeta_spec (p ^ k * m) ℚ_[p] L).pow
    (Nat.mul_pos (pow_pos hp.out.pos k) (NeZero.pos m)) (mul_comm _ _)

include hp in
theorem zeta_pow_pk :
    IsPrimitiveRoot ((IsCyclotomicExtension.zeta (p ^ k * m) ℚ_[p] L) ^ (p ^ k)) m :=
  (IsCyclotomicExtension.zeta_spec (p ^ k * m) ℚ_[p] L).pow
    (Nat.mul_pos (pow_pos hp.out.pos k) (NeZero.pos m)) rfl

instance neZero_pow : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

/-- The action on `μ_{p^k}` and on `μ_m`: `g ↦ (a, b)` with `g ζ₁ = ζ₁^a`, `g ζ₂ = ζ₂^b`. -/
noncomputable def galToProd : Gal(L/ℚ_[p]) →* (ZMod (p ^ k))ˣ × (ZMod m)ˣ :=
  ((zeta_pow_m (p := p) (L := L) k m).autToPow ℚ_[p]).prod
    ((zeta_pow_pk (p := p) (L := L) k m).autToPow ℚ_[p])

omit [IsCyclotomicExtension {p ^ k * m} ℚ_[p] L] in
theorem fix_of_autToPow_eq_one {n : ℕ} [NeZero n] {μ : L} (hμ : IsPrimitiveRoot μ n)
    (g : Gal(L/ℚ_[p])) (h : hμ.autToPow ℚ_[p] g = 1) : g μ = μ := by
  rw [← hμ.autToPow_spec ℚ_[p] g, h, Units.val_one, ZMod.val_one_eq_one_mod,
    hμ.eq_orderOf, pow_mod_orderOf, pow_one]

include hcop in
theorem galToProd_injective : Function.Injective (galToProd (p := p) (L := L) k m) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  set ζ := IsCyclotomicExtension.zeta (p ^ k * m) ℚ_[p] L
  have hζ := IsCyclotomicExtension.zeta_spec (p ^ k * m) ℚ_[p] L
  have hg1 : g (ζ ^ m) = ζ ^ m :=
    fix_of_autToPow_eq_one (zeta_pow_m k m) g (congrArg Prod.fst hg)
  have hg2 : g (ζ ^ (p ^ k)) = ζ ^ (p ^ k) :=
    fix_of_autToPow_eq_one (zeta_pow_pk k m) g (congrArg Prod.snd hg)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne _)
  have hbez : ((Nat.gcd m (p ^ k) : ℕ) : ℤ) = m * Nat.gcdA m (p ^ k) + p ^ k * Nat.gcdB m (p ^ k) := by
    rw [Nat.gcd_eq_gcd_ab]; push_cast; ring
  have hgcd : Nat.gcd m (p ^ k) = 1 := (Nat.Coprime.pow_left k hcop).symm
  rw [hgcd, Nat.cast_one] at hbez
  have hdecomp : ζ = (ζ ^ m) ^ Nat.gcdA m (p ^ k) * (ζ ^ (p ^ k)) ^ Nat.gcdB m (p ^ k) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0]
    conv_lhs => rw [← zpow_one ζ]
    congr 1
  have hfix : g ζ = ζ := by
    conv_lhs => rw [hdecomp]
    rw [map_mul, map_zpow₀, map_zpow₀, hg1, hg2, ← hdecomp]
  apply hζ.autToPow_injective ℚ_[p]
  rw [map_one]
  ext
  rw [autToPow_eq_of_apply hζ g 1 (by rw [pow_one]; exact hfix)]
  simp

/-- **Disjointness.** For `p ∤ m`, the image of `Gal(ℚ_p(μ_{p^k m})/ℚ_p)` in
`(ℤ/p^k)ˣ × (ℤ/m)ˣ` is `(ℤ/p^k)ˣ × ⟨p⟩`. -/
theorem range_galToProd :
    (galToProd (p := p) (L := L) k m).range =
      (⊤ : Subgroup (ZMod (p ^ k))ˣ).prod (Subgroup.zpowers (ZMod.unitOfCoprime p hcop)) := by
  have hm : ¬ p ∣ m := (Nat.Prime.coprime_iff_not_dvd hp.out).mp hcop
  have hle : (galToProd (p := p) (L := L) k m).range ≤
      (⊤ : Subgroup (ZMod (p ^ k))ˣ).prod (Subgroup.zpowers (ZMod.unitOfCoprime p hcop)) := by
    rintro _ ⟨g, rfl⟩
    refine ⟨Subgroup.mem_top _, ?_⟩
    have := range_autToPow_eq_zpowers' p L hm (zeta_pow_pk (p := p) (L := L) k m)
    have hmem : (zeta_pow_pk (p := p) (L := L) k m).autToPow ℚ_[p] g ∈
        ((zeta_pow_pk (p := p) (L := L) k m).autToPow ℚ_[p]).range := ⟨g, rfl⟩
    rw [this] at hmem
    exact hmem
  have hcardG : Nat.card (galToProd (p := p) (L := L) k m).range = Module.finrank ℚ_[p] L := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact Nat.card_congr (Equiv.ofInjective _ (galToProd_injective k m hcop)).symm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hcardG, card_subgroup_prod, Subgroup.card_top, Nat.card_zpowers,
    Nat.card_eq_fintype_card (α := (ZMod (p ^ k))ˣ), ZMod.card_units_eq_totient]
  exact totient_mul_orderOf_le_finrank p L hcop (zeta_pow_m (p := p) (L := L) k m)
    (zeta_pow_pk (p := p) (L := L) k m)

/-- **The Galois group of `ℚ_p(μ_{p^k m})`** for `p ∤ m`:
`Gal(L/ℚ_p) ≃* (ℤ/p^k)ˣ × ⟨p⟩`, through the action on `μ_{p^k}` and `μ_m`. -/
noncomputable def galEquivProd : Gal(L/ℚ_[p]) ≃*
    ((⊤ : Subgroup (ZMod (p ^ k))ˣ).prod (Subgroup.zpowers (ZMod.unitOfCoprime p hcop)) :
      Subgroup ((ZMod (p ^ k))ˣ × (ZMod m)ˣ)) :=
  (MonoidHom.ofInjective (galToProd_injective (p := p) (L := L) k m hcop)).trans
    (MulEquiv.subgroupCongr (range_galToProd k m hcop))

/-- **Degree.** `[ℚ_p(μ_{p^k m}):ℚ_p] = φ(p^k) · ord_m(p)` for `p ∤ m`. -/
theorem finrank_eq_totient_mul_orderOf :
    Module.finrank ℚ_[p] L = (p ^ k).totient * orderOf (ZMod.unitOfCoprime p hcop) := by
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr (galEquivProd (L := L) k m hcop).toEquiv,
    card_subgroup_prod, Subgroup.card_top, Nat.card_zpowers,
    Nat.card_eq_fintype_card (α := (ZMod (p ^ k))ˣ), ZMod.card_units_eq_totient]


/-- `galToProd` is the action on `μ_{p^k}`: `g x = x^a` for every `x` with `x^{p^k} = 1`. -/
theorem galToProd_fst_spec (g : Gal(L/ℚ_[p])) (x : L) (hx : x ^ (p ^ k) = 1) :
    g x = x ^ (((galToProd (p := p) (L := L) k m g).1 : ZMod (p ^ k))).val := by
  obtain ⟨i, -, rfl⟩ := (zeta_pow_m (p := p) (L := L) k m).eq_pow_of_pow_eq_one hx
  rw [map_pow, ← (zeta_pow_m (p := p) (L := L) k m).autToPow_spec ℚ_[p] g]
  simp only [galToProd, MonoidHom.prod_apply]
  simp only [← pow_mul]
  ring_nf

/-- `galToProd` is the action on `μ_m`: `g y = y^b` for every `y` with `y^m = 1`. -/
theorem galToProd_snd_spec (g : Gal(L/ℚ_[p])) (y : L) (hy : y ^ m = 1) :
    g y = y ^ (((galToProd (p := p) (L := L) k m g).2 : ZMod m)).val := by
  obtain ⟨i, -, rfl⟩ := (zeta_pow_pk (p := p) (L := L) k m).eq_pow_of_pow_eq_one hy
  rw [map_pow, ← (zeta_pow_pk (p := p) (L := L) k m).autToPow_spec ℚ_[p] g]
  simp only [galToProd, MonoidHom.prod_apply]
  simp only [← pow_mul]
  ring_nf

omit [NeZero m] [IsCyclotomicExtension {p ^ k * m} ℚ_[p] L] in
/-- **Compatibility with restriction.** For a subextension `K` of level `p^{k'} m'`
(`k' ≤ k`, `m' ∣ m`), restriction `Gal(L/ℚ_p) → Gal(K/ℚ_p)` corresponds to reduction
`(ℤ/p^k)ˣ × (ℤ/m)ˣ → (ℤ/p^{k'})ˣ × (ℤ/m')ˣ`. -/
theorem galToProd_restrict [NeZero m] [IsCyclotomicExtension {p ^ k * m} ℚ_[p] L]
    (K : Type) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
    [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (k' m' : ℕ) [NeZero m'] [IsCyclotomicExtension {p ^ k' * m'} ℚ_[p] K]
    [Algebra K L] [IsScalarTower ℚ_[p] K L] (hk : k' ≤ k) (hm : m' ∣ m) (g : Gal(L/ℚ_[p])) :
    (((galToProd (p := p) (L := K) k' m' (g.restrictNormal K)).1 : ZMod (p ^ k')) =
        ZMod.castHom (pow_dvd_pow p hk) _ ((galToProd (p := p) (L := L) k m g).1 : ZMod (p ^ k))) ∧
    (((galToProd (p := p) (L := K) k' m' (g.restrictNormal K)).2 : ZMod m') =
        ZMod.castHom hm _ ((galToProd (p := p) (L := L) k m g).2 : ZMod m)) := by
  constructor
  · set a := ((galToProd (p := p) (L := L) k m g).1 : ZMod (p ^ k))
    have h := autToPow_eq_of_apply (zeta_pow_m (p := p) (L := K) k' m') (g.restrictNormal K) a.val
      (by
        apply (algebraMap K L).injective
        rw [AlgEquiv.restrictNormal_commutes, map_pow _ _ a.val]
        refine galToProd_fst_spec (p := p) (L := L) k m g _ ?_
        rw [← map_pow, ← map_one (algebraMap K L)]
        congr 1
        obtain ⟨c, hc⟩ := pow_dvd_pow p hk
        rw [hc, pow_mul, (zeta_pow_m (p := p) (L := K) k' m').pow_eq_one, one_pow])
    simp only [galToProd, MonoidHom.prod_apply] at h ⊢
    rw [h, ZMod.castHom_apply, ZMod.cast_eq_val]
  · set b := ((galToProd (p := p) (L := L) k m g).2 : ZMod m)
    have h := autToPow_eq_of_apply (zeta_pow_pk (p := p) (L := K) k' m') (g.restrictNormal K) b.val
      (by
        apply (algebraMap K L).injective
        rw [AlgEquiv.restrictNormal_commutes, map_pow _ _ b.val]
        refine galToProd_snd_spec (p := p) (L := L) k m g _ ?_
        rw [← map_pow, ← map_one (algebraMap K L)]
        congr 1
        obtain ⟨c, hc⟩ := hm
        rw [hc, pow_mul, (zeta_pow_pk (p := p) (L := K) k' m').pow_eq_one, one_pow])
    simp only [galToProd, MonoidHom.prod_apply] at h ⊢
    rw [h, ZMod.castHom_apply, ZMod.cast_eq_val]

end Disj

end GlueSqrtDisj

#print axioms GlueSqrtDisj.totient_mul_orderOf_le_finrank
#print axioms GlueSqrtDisj.galToProd_injective
#print axioms GlueSqrtDisj.range_galToProd
#print axioms GlueSqrtDisj.finrank_eq_totient_mul_orderOf
#print axioms GlueSqrtDisj.galEquivProd
#print axioms GlueSqrtDisj.galToProd_fst_spec
#print axioms GlueSqrtDisj.galToProd_snd_spec
#print axioms GlueSqrtDisj.galToProd_restrict
