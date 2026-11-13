import ZInQKernel.HDecomp.Objects
import Mathlib.AlgebraicGeometry.Group.Smooth
import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety

/-! The extra smoothness in PkgI2 is a theorem, not an extra axiom.
The source predicate is Stacks Tag 03RO. Smoothness is Mathlib's
`AlgebraicGeometry.smooth_of_grpObj` (geometrically reduced + locally finite type).
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace AxiomBridge

variable {k : Type u} [Field k]

/-- A proper, geometrically integral group scheme over a field satisfies PkgI2. -/
theorem pkgI2_of_proper_geometricallyIntegral
    (A : Over (Spec (.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] : PkgI2.IsAbelianVariety (Grp.mk A) := by
  have : GrpObj (Over.mk A.hom) := inferInstanceAs (GrpObj A)
  exact ⟨inferInstance, smooth_of_grpObj A.hom, inferInstance⟩

/-- Stacks' abelian-variety predicate implies the PkgI2 predicate. -/
theorem pkgI2_of_axiom (A : Over (Spec (.of k))) [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A] :
    PkgI2.IsAbelianVariety (Grp.mk A) :=
  pkgI2_of_proper_geometricallyIntegral A

/-- Dropping PkgI2's smoothness field recovers the Stacks predicate. -/
theorem axiom_of_pkgI2 (A : Grp (Over (Spec (.of k))))
    (h : PkgI2.IsAbelianVariety A) : AlgebraicGeometry.IsAbelianVariety k A.X := by
  have : IsProper A.X.hom := h.proper
  have : GeometricallyIntegral A.X.hom := h.geomIntegral
  have : IsIntegral A.X.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton (f := A.X.hom)
  exact .mk (toIsProperVariety := .mk (toIsVariety := .mk))

/-- The two abelian-variety predicates are equivalent on the same group scheme. -/
theorem abelianVariety_iff (A : Grp (Over (Spec (.of k)))) :
    AlgebraicGeometry.IsAbelianVariety k A.X ↔ PkgI2.IsAbelianVariety A := by
  constructor
  · intro h
    let := h
    exact pkgI2_of_axiom A.X
  · exact axiom_of_pkgI2 A

end AxiomBridge

#print axioms AxiomBridge.pkgI2_of_proper_geometricallyIntegral
#print axioms AxiomBridge.pkgI2_of_axiom
#print axioms AxiomBridge.axiom_of_pkgI2
#print axioms AxiomBridge.abelianVariety_iff
