import ZInQKernel.Contrib.Herbrand.Restriction

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described at
https://www.apache.org/licenses/LICENSE-2.0 .
Authors: The Tau Ceti contributors

Modified for this project: minimal ring-valued normalization arguments inspired
by TauCeti/RingTheory/DiscreteValuationRing/Basic.lean and
TauCeti/NumberTheory/LocalField/RamificationIndex.lean at
 a6027b1d24fcb935c53bd5b50d11b40991cda418.
All objects below are the actual finite-DVR objects of `PkgI6`, on Mathlib 4.35.
-/

namespace ZInQ.Contrib.Herbrand

open IsLocalRing

section DVR

variable {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

/-- The ideal-power definition agrees with normalized additive valuation. -/
theorem mem_maximalIdeal_pow_iff_le_addVal {n : ℕ} {x : S} :
    x ∈ maximalIdeal S ^ n ↔ (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal S x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, hϖ.addVal_pow]

end DVR

section FiniteDVR

variable (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [Module.Finite A B] [Module.IsTorsionFree A B]

/-- The ideal-theoretic ramification index, with the top valuation normalized at its own
uniformizer. -/
noncomputable abbrev ramificationIndex : ℕ := (maximalIdeal B).ramificationIdx A

/-- The maximal ideal downstairs generates exactly the ramification-index power upstairs. -/
theorem map_maximalIdeal_eq_power :
    (maximalIdeal A).map (algebraMap A B) = maximalIdeal B ^ ramificationIndex A B := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hπmap : algebraMap A B π ≠ 0 := by
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A B)).mpr hπ.ne_zero
  obtain ⟨n, w, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπmap hϖ
  have hmap : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B ^ n := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hn,
      Ideal.span_singleton_mul_left_unit w.isUnit, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have he : ramificationIndex A B = n := by
    rw [ramificationIndex, ← Ideal.ramificationIdx'_eq_ramificationIdx
      (maximalIdeal A) (maximalIdeal B) (IsDiscreteValuationRing.not_a_field A)]
    refine Ideal.ramificationIdx'_spec hmap.le fun hle => ?_
    rw [hmap, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
      Ideal.span_singleton_le_span_singleton, pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit] at hle
    omega
  rw [he, hmap]

omit [IsDomain A] [IsDiscreteValuationRing A] [Module.IsTorsionFree A B] in
theorem ramificationIndex_pos : 0 < ramificationIndex A B :=
  (maximalIdeal B).ramificationIdx_pos A

/-- Every uniformizer of the base has valuation exactly `e` upstairs. -/
theorem addVal_algebraMap_irreducible {π : A} (hπ : Irreducible π) :
    IsDiscreteValuationRing.addVal B (algebraMap A B π) = ramificationIndex A B := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hspan : Ideal.span {algebraMap A B π} = Ideal.span {ϖ ^ ramificationIndex A B} := by
    simpa only [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] using map_maximalIdeal_eq_power A B
  have hass := Ideal.span_singleton_eq_span_singleton.mp hspan
  rw [(IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr hass, hϖ.addVal_pow]

/-- The exact normalization bridge `v_B(a)=e(B/A) v_A(a)`, including `a=0`. -/
theorem addVal_algebraMap (a : A) :
    IsDiscreteValuationRing.addVal B (algebraMap A B a) =
      ramificationIndex A B • IsDiscreteValuationRing.addVal A a := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  rcases eq_or_ne a 0 with rfl | ha
  · simp [ramificationIndex_pos A B |>.ne']
  obtain ⟨n, w, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  have hw : IsDiscreteValuationRing.addVal B (algebraMap A B (w : A)) = 0 :=
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr (IsUnit.map _ w.isUnit)
  rw [ha, map_mul, map_pow, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_pow, hw, zero_add, addVal_algebraMap_irreducible A B hπ,
    IsDiscreteValuationRing.addVal_def' w hπ n]
  simp [nsmul_eq_mul, mul_comm]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Perfectness suffices for the residue comparison; finite residue is not assumed. -/
theorem natCard_lowerRam_zero [PerfectField (ResidueField A)]
    [IsGalois (FractionRing A) (FractionRing B)] :
    Nat.card (PkgI6.lowerRam A B 0) = ramificationIndex A B := by
  have : IsGaloisGroup (B ≃ₐ[A] B) A B := ringAut_isGaloisGroup A B
  have : IsFractionRing (ResidueField A) (maximalIdeal A).ResidueField := by
    change IsFractionRing (A ⧸ maximalIdeal A) (maximalIdeal A).ResidueField
    infer_instance
  have : PerfectField (maximalIdeal A).ResidueField :=
    PerfectField.of_ringEquiv
      (IsFractionRing.algEquiv (ResidueField A) (ResidueField A)
        (maximalIdeal A).ResidueField).toRingEquiv
  have : Algebra.HasSeparableResidueFieldsAt A B (maximalIdeal A) := inferInstance
  simp only [PkgI6.lowerRam, zero_add, pow_one]
  change Nat.card ((maximalIdeal B).inertia (B ≃ₐ[A] B)) = _
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := B ≃ₐ[A] B) (maximalIdeal A),
    Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal A) (maximalIdeal B) (B ≃ₐ[A] B)]

end FiniteDVR

end ZInQ.Contrib.Herbrand

#print axioms ZInQ.Contrib.Herbrand.addVal_algebraMap
#print axioms ZInQ.Contrib.Herbrand.natCard_lowerRam_zero
