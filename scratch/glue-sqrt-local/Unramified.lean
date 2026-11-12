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

end GlueSqrtLocal

#print axioms GlueSqrtLocal.isLocalRing_integralClosure
#print axioms GlueSqrtLocal.exists_frobenius
#print axioms GlueSqrtLocal.pow_frobenius_of_isLocalRing
#print axioms GlueSqrtLocal.range_autToPow_eq_zpowers
#print axioms GlueSqrtLocal.range_autToPow_eq_zpowers'
#print axioms GlueSqrtLocal.pow_frobenius
