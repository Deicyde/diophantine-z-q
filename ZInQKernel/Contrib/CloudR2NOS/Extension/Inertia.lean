import ZInQKernel.Contrib.CloudR2NOS.Valuation.Points

/-!
# Scalar restriction of the actual inertia predicate

Arithmetic join for applying the supplied-model NOS converse upstairs in an
intermediate field. Restricting an extension-field algebra automorphism to the
original base keeps the SAME valuation ring, residue action, and underlying
map. This does not construct a henselization, a Néron model, or good descent.
-/

noncomputable section

open scoped Pointwise

namespace ZInQ.Contrib.CloudR2NOS.Extension

universe u

/-- Inertia over an extension field maps to inertia over the original base,
on the same valuation ring and underlying automorphism. -/
theorem isInertia_restrictScalars
    {K E Ω : Type u} [Field K] [Field E] [Field Ω]
    [Algebra K E] [Algebra E Ω] [Algebra K Ω] [IsScalarTower K E Ω]
    (w : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω) (hσ : PkgI2.IsInertia w σ) :
    PkgI2.IsInertia w (σ.restrictScalars K) := by
  have hmem : σ ∈ ZInQ.Contrib.CloudR2NOS.Valuation.inertiaSubgroupIn (K := E) w :=
    (ZInQ.Contrib.CloudR2NOS.Valuation.isInertia_iff_mem_inertiaSubgroupIn w σ).mp hσ
  have hstableE : σ • w = w := by
    obtain ⟨hd, _⟩ := hσ
    exact hd
  have hstableK : (σ.restrictScalars K) • w = w := by
    change σ • w = w
    exact hstableE
  apply (ZInQ.Contrib.CloudR2NOS.Valuation.isInertia_iff_mem_inertiaSubgroupIn w
    (σ.restrictScalars K)).mpr
  apply ZInQ.Contrib.CloudR2NOS.Valuation.mem_inertiaSubgroupIn_of_valuation_sub_lt_one
    w hstableK
  intro a ha
  exact (ZInQ.Contrib.CloudR2NOS.Valuation.valuation_sub_lt_one_of_mem_inertiaSubgroupIn
    (K := E) w hmem ha).2

end ZInQ.Contrib.CloudR2NOS.Extension

#print axioms ZInQ.Contrib.CloudR2NOS.Extension.isInertia_restrictScalars
