import ZInQKernel.Contrib.CloudR2Poincare.L6.FaceInitialFacts
import ZInQKernel.Contrib.CloudR2Poincare.L1.SectionsTriviality

/-! Actual native positive-H0 criterion for a residue-fibre bundle. The proved
all-dimensional native two-section criterion is reused, not duplicated. -/
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules
namespace ZInQ.Contrib.CloudR2Poincare.L6

/-- Positive ACTUAL H0 for a line bundle and its native dual forces its actual
Picard class to be one, over every field and in every dimension. -/
theorem nativePicardClass_eq_one_of_positiveHZero_dual
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] [GeometricallyIntegral f] (M : X.Modules) [M.IsInvertible] :
    letI : X.Over (Spec (.of k)) := ⟨f⟩
    1 ≤ Module.finrank k (M.H 0) → 1 ≤ Module.finrank k (Mᵛ.H 0) → Scheme.Pic.mk M = 1 := by
  letI : X.Over (Spec (.of k)) := ⟨f⟩
  intro hM hD
  haveI : Module.Finite k (M.H 0) := Module.finite_of_finrank_pos (by omega)
  haveI : Module.Finite k (Mᵛ.H 0) := Module.finite_of_finrank_pos (by omega)
  haveI : Nontrivial (M.H 0) :=
    (show 0 < Module.finrank k (M.H 0) ↔ Nontrivial (M.H 0) from Module.finrank_pos_iff).mp (by omega)
  haveI : Nontrivial (Mᵛ.H 0) :=
    (show 0 < Module.finrank k (Mᵛ.H 0) ↔ Nontrivial (Mᵛ.H 0) from Module.finrank_pos_iff).mp (by omega)
  have hS : Nontrivial Γ(M, ⊤) := (Scheme.Modules.H.zeroLinearEquiv M).symm.toEquiv.nontrivial
  have hT : Nontrivial Γ(Mᵛ, ⊤) := (Scheme.Modules.H.zeroLinearEquiv Mᵛ).symm.toEquiv.nontrivial
  obtain ⟨e⟩ :=
    (ZInQ.Contrib.CloudR2Poincare.L1.nonempty_iso_unit_iff_nontrivial_globalSections f M).mpr ⟨hS, hT⟩
  exact ((Scheme.Pic.mk_eq_mk_iff M (Scheme.Modules.unit X)).mpr ⟨e⟩).trans
    (Scheme.Pic.one_eq_mk_unit).symm

end ZInQ.Contrib.CloudR2Poincare.L6
