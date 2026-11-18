import DiscreteExtensionV003

/-!
# Discrete valuation rings in finite field extensions

A cyclic group of nonzero values, together with a genuinely nontrivial valuation,
produces a principal maximal ideal and a discrete valuation ring. The generator
is oriented to have value strictly less than one; its inverse is used when necessary.
-/

noncomputable section
set_option autoImplicit false

namespace FiniteExtensionValuation

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- Units in the base are exactly the elements whose images have value one. -/
theorem base_unit_iff (O : ValuationSubring K) (w : ValuationSubring M)
    (hw : w.comap (algebraMap K M) = O) (a : O) :
    IsUnit a ↔ w.valuation (algebraMap K M (a : K)) = 1 := by
  constructor
  · intro h
    obtain ⟨u, rfl⟩ := h
    exact WildTameCharacter.val_unit_eq_one O w hw u
  · intro h
    have ha : (a : K) ≠ 0 := by
      intro h0
      simp [h0] at h
    have hi' : (a : K)⁻¹ ∈ w.comap (algebraMap K M) := by
      rw [ValuationSubring.mem_comap, ← w.valuation_le_one_iff]
      rw [map_inv₀, map_inv₀, h, inv_one]
    have hi : (a : K)⁻¹ ∈ O := by simpa only [hw] using hi'
    refine IsUnit.of_mul_eq_one (⟨(a : K)⁻¹, hi⟩ : O) ?_
    apply Subtype.ext
    exact mul_inv_cancel₀ ha

/-- A base uniformizer has positive order for the actual extended valuation. -/
theorem base_uniformizer_value (O : ValuationSubring K) (w : ValuationSubring M)
    (hw : w.comap (algebraMap K M) = O) {a : O} (ha : Irreducible a) :
    0 < w.valuation (algebraMap K M (a : K)) ∧
      w.valuation (algebraMap K M (a : K)) < 1 := by
  have hmem : algebraMap K M (a : K) ∈ w := by
    rw [← ValuationSubring.mem_comap, hw]
    exact a.2
  refine ⟨(Valuation.pos_iff _).2 ?_, lt_of_le_of_ne ((w.valuation_le_one_iff _).2 hmem) ?_⟩
  · exact (map_ne_zero _).2 (fun h => ha.ne_zero (Subtype.ext h))
  · exact fun h => ha.not_isUnit ((base_unit_iff O w hw a).2 h)

/-- Orient a cyclic generator by the ordered value group, not by an arbitrary choice. -/
theorem exists_oriented_generator (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O)
    (hcyc : ∃ π : M, π ≠ 0 ∧ ∀ x : M, x ≠ 0 →
      ∃ k : ℤ, w.valuation x = w.valuation π ^ k) :
    ∃ π : w, (π : M) ≠ 0 ∧ w.valuation (π : M) < 1 ∧
      ∀ x : M, x ≠ 0 → ∃ k : ℤ, w.valuation x = w.valuation (π : M) ^ k := by
  obtain ⟨p, hp0, hp⟩ := hcyc
  have hp1 : w.valuation p ≠ 1 := by
    intro h
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hlt := (base_uniformizer_value O w hw ha).2
    obtain ⟨k, hk⟩ := hp (algebraMap K M (a : K))
      ((map_ne_zero _).2 (fun h0 => ha.ne_zero (Subtype.ext h0)))
    rw [h, one_zpow] at hk
    rw [hk] at hlt
    exact lt_irrefl _ hlt
  rcases lt_or_gt_of_ne hp1 with hlt | hgt
  · refine ⟨⟨p, (w.valuation_le_one_iff p).1 hlt.le⟩, hp0, hlt, hp⟩
  · have hpi : w.valuation p⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one₀ (lt_trans zero_lt_one hgt) |>.2 hgt
    refine ⟨⟨p⁻¹, (w.valuation_le_one_iff _).1 hpi.le⟩, inv_ne_zero hp0, hpi, ?_⟩
    intro x hx
    obtain ⟨k, hk⟩ := hp x hx
    refine ⟨-k, ?_⟩
    rw [map_inv₀, inv_zpow, zpow_neg, inv_inv]
    exact hk

/-- Nonzero elements of the valuation ring have nonnegative integral orders. -/
theorem exists_nat_power_value (w : ValuationSubring M) (π : w)
    (hπ0 : (π : M) ≠ 0) (hπ : w.valuation (π : M) < 1)
    (hcyc : ∀ x : M, x ≠ 0 → ∃ k : ℤ,
      w.valuation x = w.valuation (π : M) ^ k) (x : w) (hx : x ≠ 0) :
    ∃ n : ℕ, w.valuation (x : M) = w.valuation (π : M) ^ n := by
  obtain ⟨k, hk⟩ := hcyc x (fun h => hx (Subtype.ext h))
  have hk0 : 0 ≤ k := by
    apply (zpow_le_one_iff_right_of_lt_one₀ ((Valuation.pos_iff _).2 hπ0) hπ).1
    rw [← hk]
    exact w.valuation_le_one x
  refine ⟨k.toNat, ?_⟩
  rw [← zpow_natCast, Int.toNat_of_nonneg hk0]
  exact hk

/-- The oriented generator generates the actual maximal ideal. -/
theorem maximalIdeal_eq_span (w : ValuationSubring M) (π : w)
    (hπ0 : (π : M) ≠ 0) (hπ : w.valuation (π : M) < 1)
    (hcyc : ∀ x : M, x ≠ 0 → ∃ k : ℤ,
      w.valuation x = w.valuation (π : M) ^ k) :
    IsLocalRing.maximalIdeal w = Ideal.span {π} := by
  apply le_antisymm
  · intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    obtain ⟨n, hn⟩ := exists_nat_power_value w π hπ0 hπ hcyc x hx0
    have hn0 : n ≠ 0 := by
      intro h0
      have hlt := (w.valuation_lt_one_iff x).1 hx
      rw [hn, h0, pow_zero] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hle : w.valuation (x : M) ≤ w.valuation (π : M) := by
      rw [hn, pow_succ]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (pow_le_one₀ zero_le hπ.le) (show 0 ≤ w.valuation (π : M) from zero_le)
    obtain ⟨a, ha⟩ := (w.valuation_le_iff x π).1 hle
    rw [Ideal.mem_span_singleton]
    refine ⟨a, ?_⟩
    apply Subtype.ext
    change (x : M) = (π : M) * (a : M)
    simpa only [mul_comm] using ha.symm
  · rw [Ideal.span_singleton_le_iff_mem]
    exact (w.valuation_lt_one_iff π).2 hπ

/-- Cyclic values and a nontrivial oriented generator produce the DVR class. -/
theorem discreteValuationRing_of_oriented_generator (w : ValuationSubring M) (π : w)
    (hπ0 : (π : M) ≠ 0) (hπ : w.valuation (π : M) < 1)
    (hcyc : ∀ x : M, x ≠ 0 → ∃ k : ℤ,
      w.valuation x = w.valuation (π : M) ^ k) : IsDiscreteValuationRing w := by
  have hirr : Irreducible π :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π
      (fun h => hπ0 (congrArg Subtype.val h)) (maximalIdeal_eq_span w π hπ0 hπ hcyc)
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨π, hirr, ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := exists_nat_power_value w π hπ0 hπ hcyc x hx
  have heq : w.valuation (x : M) = w.valuation ((π ^ n : w) : M) := by
    simpa only [SubmonoidClass.coe_pow, map_pow] using hn
  obtain ⟨u, hu⟩ := (w.valuation_eq_iff x (π ^ n)).1 heq
  refine ⟨n, u, ?_⟩
  apply Subtype.ext
  change (π : M) ^ n * (u : M) = (x : M)
  simpa only [mul_comm] using hu

/-- Every valuation ring over a DVR in a finite field extension is an actual DVR,
including inseparable and wildly ramified finite extensions. -/
theorem finite_extension_isDiscreteValuationRing [FiniteDimensional K M]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O) :
    IsDiscreteValuationRing w := by
  obtain ⟨π, hπ0, hπ, hcyc⟩ := exists_oriented_generator O w hw
    (WildTameCharacter.exists_uniformizer_of_finiteDimensional O w hw)
  exact discreteValuationRing_of_oriented_generator w π hπ0 hπ hcyc

/-- The ambient extension field is the fraction field of this very valuation ring. -/
theorem extended_fraction_field (w : ValuationSubring M) : IsFractionRing w M := inferInstance

/-- Noetherianity is a conclusion of the finite-extension construction. -/
theorem finite_extension_isNoetherianRing [FiniteDimensional K M]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O) :
    IsNoetherianRing w := by
  letI := finite_extension_isDiscreteValuationRing O w hw
  infer_instance

end FiniteExtensionValuation
