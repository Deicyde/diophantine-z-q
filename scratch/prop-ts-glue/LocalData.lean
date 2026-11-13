import Mathlib

/-! prop-ts-glue: development file for `SNLocalData` (imports Mathlib only; the result is pasted
into `PropTSGlue.lean`). -/

open Polynomial

noncomputable section

namespace PropTSGlueDev

abbrev zxMap (E : Type) [Field E] [Algebra ℚ[X] E] : ℤ[X] →+* E :=
  (algebraMap ℚ[X] E).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))

theorem zxMap_injective (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] : Function.Injective (zxMap E) := by
  intro a b h
  simp only [zxMap, RingHom.comp_apply, IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E] at h
  have h1 := (algebraMap (RatFunc ℚ) E).injective h
  have h2 := (IsFractionRing.injective ℚ[X] (RatFunc ℚ)) h1
  exact Polynomial.map_injective _ Int.cast_injective h2

@[reducible] noncomputable def locAlg (E : Type) [Field E] [Algebra (RatFunc ℚ) E]
    [Algebra ℚ[X] E] [IsScalarTower ℚ[X] (RatFunc ℚ) E] (m : Ideal ℤ[X]) [m.IsPrime] :
    Algebra (Localization.AtPrime m) E :=
  (IsLocalization.lift (M := m.primeCompl) (S := Localization.AtPrime m) (g := zxMap E)
    (fun y => by
      rw [isUnit_iff_ne_zero]
      intro h
      apply y.2
      rw [(zxMap_injective E) (h.trans (map_zero _).symm)]
      exact m.zero_mem)).toAlgebra

/-- `ℚ(X)` is the fraction field of `ℤ[X]` (through `ℤ[X] → ℚ[X] → ℚ(X)`). -/
theorem isFractionRing_zx :
    letI : Algebra ℤ[X] (RatFunc ℚ) := (zxMap (RatFunc ℚ)).toAlgebra
    IsFractionRing ℤ[X] (RatFunc ℚ) := by
  letI : Algebra ℤ[X] (RatFunc ℚ) := (zxMap (RatFunc ℚ)).toAlgebra
  have hinj : Function.Injective (algebraMap ℤ[X] (RatFunc ℚ)) := zxMap_injective (RatFunc ℚ)
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rw [isUnit_iff_ne_zero]
    intro h
    exact nonZeroDivisors.coe_ne_zero y (hinj (h.trans (map_zero _).symm))
  · intro z
    obtain ⟨⟨P, Q⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors ℚ[X]) z
    obtain ⟨bP, hbPM, hbP⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) P
    obtain ⟨bQ, hbQM, hbQ⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ)
      (Q : ℚ[X])
    set P' := IsLocalization.integerNormalization (nonZeroDivisors ℤ) P
    set Q' := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (Q : ℚ[X])
    have hbP0 : bP ≠ 0 := nonZeroDivisors.ne_zero hbPM
    have hbQ0 : bQ ≠ 0 := nonZeroDivisors.ne_zero hbQM
    have hQ0 : (Q : ℚ[X]) ≠ 0 := nonZeroDivisors.coe_ne_zero Q
    have hmapQ : Q'.map (Int.castRingHom ℚ) = C (bQ : ℚ) * Q := by
      rw [← smul_eq_C_mul]
      simpa [Algebra.smul_def] using hbQ
    have hmapP : P'.map (Int.castRingHom ℚ) = C (bP : ℚ) * P := by
      rw [← smul_eq_C_mul]
      simpa [Algebra.smul_def] using hbP
    have hy : C bP * Q' ∈ nonZeroDivisors ℤ[X] := by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      refine mul_ne_zero (by simpa using hbP0) ?_
      intro h0
      have := hmapQ
      rw [h0, Polynomial.map_zero] at this
      exact mul_ne_zero (by simpa using hbQ0) hQ0 this.symm
    refine ⟨⟨C bQ * P', ⟨_, hy⟩⟩, ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, zxMap, RingHom.comp_apply, coe_mapRingHom,
      Polynomial.map_mul, Polynomial.map_C, hmapP, hmapQ, map_mul, eq_intCast]
    rw [← hz]
    simp only [map_intCast, Int.cast_id, Polynomial.map_intCast]
    ring
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩

/-- **`SNLocalData` holds** (the normalization of `ℤ[X]_m` in `E` is normal, finite, and
contains `ℤ[X]_m`). -/
theorem snLocalData_aux (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (m : Ideal ℤ[X]) [m.IsMaximal] :
    letI := locAlg E m
    IsIntegrallyClosed (integralClosure (Localization.AtPrime m) E) ∧
    Module.Finite (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E) ∧
    Function.Injective
      (algebraMap (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E)) := by
  letI iE : Algebra (Localization.AtPrime m) E := locAlg E m
  letI iK : Algebra (Localization.AtPrime m) (RatFunc ℚ) := locAlg (RatFunc ℚ) m
  letI iZ : Algebra ℤ[X] (RatFunc ℚ) := (zxMap (RatFunc ℚ)).toAlgebra
  have hZ : IsFractionRing ℤ[X] (RatFunc ℚ) := isFractionRing_zx
  have hT1 : IsScalarTower ℤ[X] (Localization.AtPrime m) (RatFunc ℚ) := by
    apply IsScalarTower.of_algebraMap_eq'
    exact (IsLocalization.lift_comp _).symm
  have hfr : IsFractionRing (Localization.AtPrime m) (RatFunc ℚ) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m.primeCompl _ _
  have hT2 : IsScalarTower (Localization.AtPrime m) (RatFunc ℚ) E := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext m.primeCompl
    rw [RingHom.comp_assoc]
    change (IsLocalization.lift _).comp (algebraMap ℤ[X] (Localization.AtPrime m)) =
      (algebraMap (RatFunc ℚ) E).comp
        ((IsLocalization.lift _).comp (algebraMap ℤ[X] (Localization.AtPrime m)))
    rw [IsLocalization.lift_comp, IsLocalization.lift_comp]
    simp only [zxMap, ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have hic : IsIntegrallyClosed (Localization.AtPrime m) :=
    isIntegrallyClosed_of_isLocalization _ m.primeCompl m.primeCompl_le_nonZeroDivisors
  refine ⟨integralClosure.isIntegrallyClosedOfFiniteExtension (RatFunc ℚ),
    IsIntegralClosure.finite (Localization.AtPrime m) (RatFunc ℚ) E
      (integralClosure (Localization.AtPrime m) E), ?_⟩
  intro a b h
  have h1 := congrArg Subtype.val h
  simp only [IntermediateField.algebraMap_apply, Subalgebra.coe_algebraMap] at h1
  rw [IsScalarTower.algebraMap_apply (Localization.AtPrime m) (RatFunc ℚ) E,
    IsScalarTower.algebraMap_apply (Localization.AtPrime m) (RatFunc ℚ) E] at h1
  exact IsFractionRing.injective (Localization.AtPrime m) (RatFunc ℚ)
    ((algebraMap (RatFunc ℚ) E).injective h1)

end PropTSGlueDev

#print axioms PropTSGlueDev.isFractionRing_zx
#print axioms PropTSGlueDev.snLocalData_aux
