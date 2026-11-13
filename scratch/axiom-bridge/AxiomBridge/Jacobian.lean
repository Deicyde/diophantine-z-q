import AxiomBridge.AbelianVariety
import Mordell.Jacobian.Existence
import Mordell.Jacobian.Dimension

open CategoryTheory AlgebraicGeometry

universe u

namespace AxiomBridge

variable {k : Type u} [Field k]

/-- Every Faltings Jacobian has an underlying PkgI2 abelian variety. -/
theorem jacobian_isAbelianVariety {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [Faltings.IsSmoothProjectiveCurve k f] (J : Faltings.Jacobian k f) :
    PkgI2.IsAbelianVariety (Grp.mk J.J) := by
  let := J.isAbelianVariety
  exact pkgI2_of_axiom J.J

/-- A degree-one rational divisor gives a PkgI2 Jacobian, unique as a representing
scheme with its Picard transformation, and with dimension equal to the genus. -/
theorem exists_pkgI2_jacobian (X : Faltings.CurveWithDegreeOneDivisor k) :
    (∃ J : Faltings.Jacobian k X.f,
      PkgI2.IsAbelianVariety (Grp.mk J.J) ∧
      topologicalKrullDim J.J.left = (genus X.f : WithBot ℕ∞)) ∧
    (∀ J J' : Faltings.Jacobian k X.f,
      ∃! e : J.J ≅ J'.J, J.ι ≫ yoneda.map e.hom = J'.ι) := by
  obtain ⟨⟨J⟩, huniq⟩ := Faltings.Jacobian.nonempty_and_existsUnique_iso k X
  exact ⟨⟨J, jacobian_isAbelianVariety X.f J,
    Faltings.Jacobian.topologicalKrullDim_eq_genus X J⟩, huniq⟩

end AxiomBridge

#print axioms AxiomBridge.jacobian_isAbelianVariety
#print axioms AxiomBridge.exists_pkgI2_jacobian
