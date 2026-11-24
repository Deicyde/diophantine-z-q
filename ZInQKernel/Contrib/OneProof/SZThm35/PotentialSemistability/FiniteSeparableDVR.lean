import ZInQKernel.Contrib.CloudR2NOS.Valuation.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Dvr

noncomputable section

open ZInQ.Contrib.CloudR2NOS.Valuation

namespace SZRaynaud

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (O : ValuationSubring K) (W : ValuationSubring L)
  (h : W.comap (algebraMap K L) = O)

include h in
private theorem isUnit_of_isUnit_extension
    (a : O) (b : W) (hab : (b : L) = algebraMap K L (a : K))
    (hu : IsUnit b) : IsUnit a := by
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hu
  have hy' : algebraMap K L (a : K) * (y : L) = 1 := by
    rw [← hab]
    exact congrArg Subtype.val hy
  have hv : algebraMap K L ((a : K)⁻¹) = (y : L) := by
    rw [map_inv₀]
    exact inv_eq_of_mul_eq_one_right hy'
  have hi' : (a : K)⁻¹ ∈ W.comap (algebraMap K L) := by
    rw [ValuationSubring.mem_comap, hv]
    exact y.2
  have hi : (a : K)⁻¹ ∈ O := (congrArg (fun V : ValuationSubring K => (a : K)⁻¹ ∈ V) h).mp hi'
  refine isUnit_iff_exists_inv.mpr ⟨⟨(a : K)⁻¹, hi⟩, Subtype.ext ?_⟩
  have h0 : (a : K) ≠ 0 := by
    intro he
    rw [he, map_zero, zero_mul] at hy'
    exact zero_ne_one hy'
  exact mul_inv_cancel₀ h0

include h in
/-- A valuation extending a DVR to a finite separable field is again discrete.
It is the localization of the finite integral closure at its center. -/
theorem isDiscreteValuationRing_of_finite_separable
    [IsDiscreteValuationRing O] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsDiscreteValuationRing W := by
  let B := integralClosure O L
  have hO (x : K) : algebraMap K L x ∈ W ↔ x ∈ O := by
    rw [← h, ValuationSubring.mem_comap]
  let f : B →+* W := (integralClosure O L).val.toRingHom.codRestrict W.toSubring fun b =>
    W.mem_of_valuation_le_one _ (Prufer.val_le_one_of_isIntegral O W hO b.2)
  let : Algebra B W := f.toAlgebra
  let P : Ideal B := (IsLocalRing.maximalIdeal W).comap f
  let : P.IsPrime := Ideal.IsPrime.comap f
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun x : W => (x : L)) hab
  let : IsLocalization.AtPrime W P := by
    constructor
    refine ⟨?_, ?_, ?_⟩
    · intro s
      have hs : f (s : B) ∉ IsLocalRing.maximalIdeal W := s.2
      exact not_not.mp ((IsLocalRing.mem_maximalIdeal _).not.mp hs)
    · intro x
      obtain ⟨b, s, hs, he⟩ := (Prufer.mem_iff_rep O W hO (x : L)).mp x.2
      have hu : IsUnit (f s) := (W.valuation_eq_one_iff _).mpr hs
      have hsP : s ∉ P := by
        intro hh
        exact (IsLocalRing.mem_maximalIdeal _).mp hh hu
      refine ⟨⟨b, ⟨s, hsP⟩⟩, Subtype.ext ?_⟩
      exact he
    · intro a b hab
      exact ⟨1, congrArg (1 * ·) (hf hab)⟩
  have hP : P ≠ ⊥ := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hmem : algebraMap O B π ∈ P := by
      apply (IsLocalRing.mem_maximalIdeal _).mpr
      exact fun hu => hπ.not_isUnit
        (isUnit_of_isUnit_extension O W h π (f (algebraMap O B π)) rfl hu)
    intro hP
    have h0 : algebraMap O B π = 0 := (Ideal.mem_bot.mp (hP ▸ hmem))
    have hh : algebraMap K L (π : K) = 0 := congrArg (fun x : B => (x : L)) h0
    exact hπ.ne_zero (Subtype.ext ((algebraMap K L).injective (hh.trans (map_zero _).symm)))
  let : IsDedekindDomain B := integralClosure.isDedekindDomain O K L
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP W

/-- The intermediate valuation appearing in the potential semistability
criterion is a DVR as soon as the intermediate extension is finite separable. -/
theorem isDiscreteValuationRing_intermediate_of_finite_separable
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
    (E : IntermediateField K Ω) [IsDiscreteValuationRing O]
    [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    IsDiscreteValuationRing (V.comap (algebraMap E Ω)) := by
  apply isDiscreteValuationRing_of_finite_separable O
  rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq, hV]

end SZRaynaud

#print axioms SZRaynaud.isDiscreteValuationRing_intermediate_of_finite_separable
