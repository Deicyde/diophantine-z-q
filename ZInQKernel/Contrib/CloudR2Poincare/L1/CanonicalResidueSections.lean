import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.BaseChange

/-!
# The actual canonical residue-field map on coefficient-sheaf sections

Its definition is the native tensor comparison `b ⊗ s ↦ b • pullbackSection s`.
This is the map the Grauert construction must prove bijective/nonzero; an
arbitrarily chosen objectwise cohomology isomorphism is not substituted for it.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- The canonical tensor base-change map to the actual residue-fibre sections. -/
def canonicalResidueSectionsBaseChange {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : X.Modules) (y : Y) :=
  let p := Y.fromSpecResidueField y
  letI : Algebra Γ(Y, ⊤) Γ(Spec (Y.residueField y), ⊤) := p.appTop.hom.toAlgebra
  Scheme.Modules.sectionsModuleBaseChange (IsPullback.of_hasPullback f p) M rfl (⊤ : X.Opens)

end ZInQ.Contrib.CloudR2Poincare.L1
