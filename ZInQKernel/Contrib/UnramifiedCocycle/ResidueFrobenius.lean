import ZInQKernel.Contrib.UnramifiedCocycle.ResidueRoots

/-!
# A common exponent for the actual residue action and prime-to-p root action

The residue-action construction is adapted from the actual proof of
`GlueSqrtLocal.pow_frobenius_of_isLocalRing`, PR46 revision
`e0138213a452463b950166d51d2172bc48a95a19`, FiniteLevel.lean lines 177-241
(SHA-256 e130499acca61c2722e6af2414708473980aa1625abda816dc123c617b4832d4).
This is a new, stronger owned export: the producer's public theorem only
exports root action.  The producer sources are not changed.
-/

namespace ZInQ.Contrib.UnramifiedCocycle

open Polynomial IsLocalRing
open ZInQ.Contrib.LocalSquareRoot
open scoped Pointwise

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

attribute [local instance] Ideal.Quotient.field

section Local

variable (p : Nat.Primes) (M : Type) [Field M] [Algebra ℚ_[p] M]
  [Algebra ℤ_[p] M] [IsScalarTower ℤ_[p] ℚ_[p] M]
  [FiniteDimensional ℚ_[p] M] [IsGalois ℚ_[p] M]

local notation "S" => integralClosure ℤ_[p] M

/-- The exact chosen prime is invariant because this integral closure is local. -/
theorem integralClosure_prime_stabilized (Q : Ideal S) [Q.IsMaximal]
    (τ : Gal(M/ℚ_[p])) : τ ∈ MulAction.stabilizer Gal(M/ℚ_[p]) Q := by
  let : IsLocalRing S := GlueSqrtLocal.isLocalRing_integralClosure (p : ℕ) M
  have hQeq : Q = maximalIdeal S := IsLocalRing.eq_maximalIdeal inferInstance
  rw [MulAction.mem_stabilizer_iff, hQeq]
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, IsLocalRing.mem_maximalIdeal,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  exact isUnit_map_iff (MulSemiringAction.toRingEquiv Gal(M/ℚ_[p]) S τ⁻¹) x

/-- The exponent is selected from the ACTUAL quotient stabilizer homomorphism.
It acts on every residue element, not merely on roots of unity. -/
theorem exists_residue_frobenius (Q : Ideal S) [Q.IsMaximal]
    [Q.LiesOver (maximalIdeal ℤ_[p])] (τ : Gal(M/ℚ_[p])) :
    ∃ r : ℕ, ∀ z : S,
      Ideal.Quotient.mk Q (τ • z) = (Ideal.Quotient.mk Q z) ^ ((p : ℕ) ^ r) := by
  have : Module.Finite ℤ_[p] S := IsIntegralClosure.finite ℤ_[p] ℚ_[p] M S
  have hunder : Q.under ℤ_[p] = maximalIdeal ℤ_[p] :=
    ((Ideal.liesOver_iff Q (maximalIdeal ℤ_[p])).mp inferInstance).symm
  have : Finite (ℤ_[p] ⧸ Q.under ℤ_[p]) := by
    rw [hunder]
    exact Nat.finite_of_card_ne_zero (by
      rw [GlueSqrtLocal.card_quotient_maximalIdeal (p : ℕ)]
      exact p.2.ne_zero)
  have : Module.Finite (ℤ_[p] ⧸ Q.under ℤ_[p]) (S ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite ℤ_[p] _ _
  have : Finite (S ⧸ Q) := Module.finite_of_finite (ℤ_[p] ⧸ Q.under ℤ_[p])
  have : (Q.under ℤ_[p]).IsMaximal := by rw [hunder]; infer_instance
  let : Fintype (ℤ_[p] ⧸ Q.under ℤ_[p]) := Fintype.ofFinite _
  let φ := Ideal.Quotient.stabilizerHom Q (Q.under ℤ_[p]) Gal(M/ℚ_[p])
    ⟨τ, integralClosure_prime_stabilized p M Q τ⟩
  obtain ⟨⟨r, _⟩, hr⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
    (ℤ_[p] ⧸ Q.under ℤ_[p]) (S ⧸ Q)).2 φ
  have hcard : Fintype.card (ℤ_[p] ⧸ Q.under ℤ_[p]) = (p : ℕ) := by
    rw [Fintype.card_eq_nat_card, Nat.card_congr (Ideal.quotEquivOfEq hunder).toEquiv,
      GlueSqrtLocal.card_quotient_maximalIdeal (p : ℕ)]
  refine ⟨r, ?_⟩
  intro z
  have h := congrArg (fun f => f (Ideal.Quotient.mk Q z)) hr
  simp only at h
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, hcard] at h
  beta_reduce at h
  exact h.symm

/-- The SAME exponent supplies the actual residue action and the root action. -/
theorem exists_residue_and_root_frobenius (Q : Ideal S) [Q.IsMaximal]
    [Q.LiesOver (maximalIdeal ℤ_[p])] (τ : Gal(M/ℚ_[p])) :
    ∃ r : ℕ,
      (∀ z : S, Ideal.Quotient.mk Q (τ • z) =
        (Ideal.Quotient.mk Q z) ^ ((p : ℕ) ^ r)) ∧
      (∀ m : ℕ, ¬ (p : ℕ) ∣ m → ∀ ζ : M, ζ ^ m = 1 → τ ζ = ζ ^ ((p : ℕ) ^ r)) := by
  obtain ⟨r, hr⟩ := exists_residue_frobenius p M Q τ
  refine ⟨r, hr, ?_⟩
  intro m hm ζ hζ
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have hζS : IsIntegral ℤ_[p] ζ :=
    ⟨X ^ m - C 1, monic_X_pow_sub_C 1 hm0, by simp [hζ]⟩
  let z : S := ⟨ζ, hζS⟩
  have hz : z ^ m = 1 := Subtype.ext (by simpa [z] using hζ)
  have hunder : Q.under ℤ_[p] = maximalIdeal ℤ_[p] :=
    ((Ideal.liesOver_iff Q (maximalIdeal ℤ_[p])).mp inferInstance).symm
  have hmQ : (m : S) ∉ Q := by
    intro h
    have h1 : (m : ℤ_[p]) ∈ Q.under ℤ_[p] := by
      rw [Ideal.under, Ideal.mem_comap, map_natCast]
      exact h
    rw [hunder, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast,
      ZMod.natCast_eq_zero_iff] at h1
    exact hm h1
  have hq : Ideal.Quotient.mk Q (τ • z) =
      Ideal.Quotient.mk Q (z ^ ((p : ℕ) ^ r)) := by
    rw [map_pow]
    exact hr z
  have hτz : (τ • z) ^ m = 1 := by rw [← smul_pow', hz, smul_one]
  have hzp : (z ^ ((p : ℕ) ^ r)) ^ m = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hz, one_pow]
  have he := GlueSqrtLocal.eq_of_pow_eq_one_of_sub_mem Q hτz hzp (Ideal.Quotient.eq.mp hq) hmQ
  have h := congrArg (fun s : S => (s : M)) he
  simpa only [integralClosure.coe_smul, AlgEquiv.smul_def, SubmonoidClass.coe_pow, z] using h

end Local

end ZInQ.Contrib.UnramifiedCocycle
