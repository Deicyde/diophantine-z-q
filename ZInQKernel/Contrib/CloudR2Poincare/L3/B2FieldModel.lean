import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.FieldRank

/-! The literal native H versus field-valued higher-direct-image model bridge.
No alternate Cech cohomology backend or scalar-comparison hypothesis is used. -/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits

namespace ZInQ.Contrib.CloudR2Poincare.L3
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u

/-- Vanishing of actual native H^q over a field forces the actual q-th direct
image to be a zero SHEAF, not merely a zero abstract vector space. -/
theorem isZero_higherDirectImage_overField_of_native_H_zero
    {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) (hH : Subsingleton (F.H q)) :
    IsZero ((Scheme.Modules.higherDirectImage (X ↘ Spec (.of k)) q).obj F) := by
  obtain ⟨e⟩ := Scheme.Modules.nonempty_moduleSpecΓFunctor_obj_higherDirectImage_linearEquiv_H F k q
  haveI := hH
  haveI := e.toEquiv.subsingleton
  exact (Scheme.Modules.isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero
    (Field.toIsField k) _).2 Module.finrank_zero_of_subsingleton

end ZInQ.Contrib.CloudR2Poincare.L3
