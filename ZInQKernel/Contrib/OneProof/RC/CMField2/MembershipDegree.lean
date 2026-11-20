import ZInQKernel.Contrib.OneProof.RC.CMField2.Membership
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! Degree bounds also follow from inclusion, over the quadratic base.
This does not use the conjugate-order comparison. -/

noncomputable section
open NumberField Module IntermediateField TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields

namespace ZInQ.Manuscript.RC.CMField2

/-- Ring class field membership by itself gives the bound over the quadratic field. -/
theorem singularModulus_finrank_over_base_le_of_mem (hm : SingularModulusMemRingClass)
    {K : Type} [Field K] [NumberField K] (O : NumberFieldOrder K)
    (hk : finrank ℚ K = 2) (hc : IsTotallyComplex K)
    (κ : K →+* ℂ) (I : O.invertibleProperFractionalIdeals) :
    let : Algebra K ℂ := κ.toAlgebra
    finrank K K⟮singularModulus O hk hc κ I⟯ ≤ Nat.card (Pic O) := by
  let : Algebra K ℂ := κ.toAlgebra
  obtain ⟨ι, hι, hmem⟩ := hm K O hk hc κ
  let f : ringClassField O →ₐ[K] ℂ :=
    ⟨ι, fun x => DFunLike.congr_fun hι x⟩
  let j := singularModulus O hk hc κ I
  have hle : K⟮j⟯ ≤ f.fieldRange :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (hmem I))
  rw [← finrank_ringClassField]
  let g := (AlgEquiv.ofInjective f f.injective).symm.toAlgHom.comp (IntermediateField.inclusion hle)
  exact LinearMap.finrank_le_finrank_of_injective (f := g.toLinearMap) g.injective


end ZInQ.Manuscript.RC.CMField2
