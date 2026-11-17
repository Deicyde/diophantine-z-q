import ZInQKernel.Contrib.CloudB3W17bOkaComparison.CanonicalEtaleUniqueness
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.IntrinsicResidueCore

/-!
# Actual analytic-residue uniqueness into the original canonical étale affine scheme

This is the proved open-diagonal LRS uniqueness at a genuine analytic source,
using its actual intrinsic residue evaluation. It packages the type boundary so
applications need not unfold a chosen analytification when transporting source
stalks. No model/compatibility/GAGA/algebraic-map witness is introduced.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable (p : ComplexPoint X)

/-- The actual analytic residue maps instantiate genuine unramified LRS uniqueness. -/
theorem actualEtale_analytic_residue_lrs_ext (S : AnalyticSpace.{0})
    (f g : S.toLocallyRingedSpace ⟶ (actualEtaleNativeScheme X d p).left.toLocallyRingedSpace)
    (hc : (LocallyRingedSpace.Γ.map f.op).hom.comp (actualEtaleDatum X d p).coordinateRingHomOnOpen =
      (LocallyRingedSpace.Γ.map g.op).hom.comp (actualEtaleDatum X d p).coordinateRingHomOnOpen)
    (hv : ∀ (x : S) (r : Γ((actualEtaleNativeScheme X d p).left, ⊤)),
      intrinsicEval S (U := ⊤) x trivial ((LocallyRingedSpace.Γ.map f.op).hom r) =
        intrinsicEval S (U := ⊤) x trivial ((LocallyRingedSpace.Γ.map g.op).hom r)) : f = g :=
  @actualEtale_residue_lrs_hom_ext X d inferInstance p S.toLocallyRingedSpace f g hc
    (intrinsicStalkEval S) (fun x => intrinsicStalkEval_isLocalHom S x) hv

end ZInQ.Contrib.CloudB3W17bOkaComparison
