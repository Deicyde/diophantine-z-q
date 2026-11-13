import ZInQKernel.Contrib.FrobeniusDensity.Defs
import Mathlib.FieldTheory.Galois.Profinite

/-!
# The finite normal quotient and the exact coset orientation

An open subgroup need not be normal. Passing to the normal closure of a finite
subfield gives a smaller open normal fixing subgroup, so matching its finite
Galois restriction suffices. No density or Frobenius existence is assumed here.
-/

namespace ZInQ.Contrib.FrobeniusDensity

open scoped Topology

/-- Every open subgroup contains the fixing subgroup of a finite Galois
subfield. This is the normal-core reduction needed even for nonnormal `U`. -/
theorem exists_finiteGalois_fixingSubgroup_le (U : Subgroup GQ)
    (hU : IsOpen (U : Set GQ)) :
    ∃ E : IntermediateField ℚ Qbar,
      FiniteDimensional ℚ E ∧ IsGalois ℚ E ∧ E.fixingSubgroup ≤ U := by
  obtain ⟨E, hE, hN, hsub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ Qbar (U : Set GQ)).mp
      (hU.mem_nhds U.one_mem)
  have : FiniteDimensional ℚ E := hE
  have : Normal ℚ E := hN
  exact ⟨E, hE, ⟨⟩, hsub⟩

/-- Equality of the actual finite restrictions gives the target orientation
`tau⁻¹ * sigma ∈ U`. It is not merely equality of conjugacy classes. -/
theorem inv_mul_mem_of_restrictNormal_eq (U : Subgroup GQ)
    (E : IntermediateField ℚ Qbar) [Normal ℚ E]
    (hEU : E.fixingSubgroup ≤ U) (τ σ : GQ)
    (hres : AlgEquiv.restrictNormal τ E = AlgEquiv.restrictNormal σ E) :
    τ⁻¹ * σ ∈ U := by
  apply hEU
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have heq : τ x = σ x := by
    calc
      τ x = algebraMap E Qbar (AlgEquiv.restrictNormal τ E ⟨x, hx⟩) :=
        (AlgEquiv.restrictNormal_commutes τ E ⟨x, hx⟩).symm
      _ = algebraMap E Qbar (AlgEquiv.restrictNormal σ E ⟨x, hx⟩) := by rw [hres]
      _ = σ x := AlgEquiv.restrictNormal_commutes σ E ⟨x, hx⟩
  change τ.symm (σ x) = x
  rw [← heq]
  exact AlgEquiv.symm_apply_apply τ x

end ZInQ.Contrib.FrobeniusDensity
