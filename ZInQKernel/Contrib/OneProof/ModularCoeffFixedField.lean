import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Fixed coefficients under complex field automorphisms

General Galois descent inside `ℂ`: an element of a number field fixed by every automorphism of
`ℂ` over `L` lies in `L`. Nothing about modular forms is asserted here; in particular this does
not prove the coefficient-field inclusion for oldforms. -/

namespace ModularCoeffFixedField

/-- An automorphism of the relative algebraic closure extends to the ambient algebraically
closed field, by fixing a transcendence basis and then extending to an algebraic closure. -/
theorem exists_extend_relative {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K]
    (σ : algebraicClosure F K ≃ₐ[F] algebraicClosure F K) :
    ∃ τ : K ≃ₐ[F] K, ∀ x : algebraicClosure F K, τ x = (σ x : K) := by
  let A := algebraicClosure F K
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis A K
  let B := Algebra.adjoin A (Set.range ((↑) : s → K))
  let : IsAlgClosure B K := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  let e : MvPolynomial s A ≃+* B := hs.1.aevalEquiv.toRingEquiv
  let σB : B ≃+* B := (e.symm.trans (MvPolynomial.mapEquiv s σ.toRingEquiv)).trans e
  have hB (x : A) : σB (algebraMap A B x) = algebraMap A B (σ x) := by
    change e (MvPolynomial.mapEquiv s σ.toRingEquiv (e.symm (algebraMap A B x))) = _
    have he (y : A) : e (MvPolynomial.C y) = algebraMap A B y := by
      exact hs.1.aevalEquiv.commutes y
    rw [← he x, e.symm_apply_apply, MvPolynomial.mapEquiv_apply, MvPolynomial.map_C, he]
    rfl
  let τ := IsAlgClosure.equivOfEquiv K K σB
  have hτ (x : A) : τ (algebraMap A K x) = algebraMap A K (σ x) := by
    rw [IsScalarTower.algebraMap_apply A B K, IsAlgClosure.equivOfEquiv_algebraMap, hB]
    rfl
  refine ⟨{ τ with commutes' := ?_ }, hτ⟩
  intro r
  change τ (algebraMap F K r) = algebraMap F K r
  rw [IsScalarTower.algebraMap_apply F A K, hτ, σ.commutes]

/-- The algebraic elements fixed by all ambient automorphisms over the base come from the base. -/
theorem mem_range_of_fixed {F K : Type*} [Field F] [CharZero F] [Field K] [Algebra F K]
    [IsAlgClosed K] {x : K} (hx : IsAlgebraic F x)
    (hfix : ∀ σ : K ≃ₐ[F] K, σ x = x) : x ∈ Set.range (algebraMap F K) := by
  let a : algebraicClosure F K := ⟨x, mem_algebraicClosure_iff.mpr hx⟩
  have ha : a ∈ Set.range (algebraMap F (algebraicClosure F K)) := by
    apply (InfiniteGalois.mem_range_algebraMap_iff_fixed a).mpr
    intro σ
    obtain ⟨τ, hτ⟩ := exists_extend_relative σ
    exact Subtype.ext ((hτ a).symm.trans (hfix τ))
  obtain ⟨y, hy⟩ := ha
  exact ⟨y, congrArg Subtype.val hy⟩

/-- Coefficient-field endpoint: use the actual subgroup fixing `L` pointwise. -/
theorem mem_old_of_fixed (F L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F]
    (x : F) (hfix : ∀ σ : ℂ ≃ₐ[ℚ] ℂ, σ ∈ L.fixingSubgroup → σ (x : ℂ) = x) :
    (x : ℂ) ∈ L := by
  have hxQ : IsAlgebraic ℚ (x : ℂ) :=
    (Algebra.IsIntegral.isIntegral x).map F.val |>.isAlgebraic
  have hxL : IsAlgebraic L (x : ℂ) := hxQ.tower_top L
  obtain ⟨y, hy⟩ := mem_range_of_fixed hxL (fun σ =>
    hfix (L.fixingSubgroupEquiv.symm σ).val (L.fixingSubgroupEquiv.symm σ).property)
  exact hy ▸ y.property

end ModularCoeffFixedField
