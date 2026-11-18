import ExtendedRingMapsV003

/-! # Positive ramification order and invertibility in the actual extended DVR -/

noncomputable section
set_option autoImplicit false

namespace FiniteExtensionValuation

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- A base uniformizer has strictly positive integral order, and the extended
maximal ideal powers give the literal ramification-ideal equality. -/
theorem exists_positive_ramification_index [FiniteDimensional K M]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O)
    {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ (π : w) (e : ℕ) (u : wˣ), Irreducible π ∧ 0 < e ∧
      baseHom O w hw ϖ = u * π ^ e ∧
      (IsLocalRing.maximalIdeal O).map (baseHom O w hw) = IsLocalRing.maximalIdeal w ^ e := by
  letI := finite_extension_isDiscreteValuationRing O w hw
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w
  have hbase0 : baseHom O w hw ϖ ≠ 0 := by
    intro h
    exact hϖ.ne_zero (baseHom_injective O w hw (by simpa using h))
  obtain ⟨e, u, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hbase0 hπ
  have he0 : e ≠ 0 := by
    intro h0
    have hu : IsUnit (baseHom O w hw ϖ) := by simpa [he, h0] using u.isUnit
    exact hϖ.not_isUnit (IsUnit.of_map (baseHom O w hw) ϖ hu)
  refine ⟨π, e, u, hπ, Nat.pos_of_ne_zero he0, he, ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, he,
    Ideal.span_singleton_mul_left_unit u.isUnit, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]

/-- The primes invertible at the original place stay invertible at the selected
extended place; the converse holds as well. -/
theorem natCast_isUnit_iff (O : ValuationSubring K) (w : ValuationSubring M)
    (hw : w.comap (algebraMap K M) = O) (n : ℕ) : IsUnit (n : O) ↔ IsUnit (n : w) := by
  constructor
  · intro h
    simpa only [map_natCast] using h.map (baseHom O w hw)
  · intro h
    exact IsUnit.of_map (baseHom O w hw) (n : O) (by simpa only [map_natCast] using h)

end FiniteExtensionValuation
