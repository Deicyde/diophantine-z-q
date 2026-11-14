import C10AbVarFrobenius
import C10FrobeniusGeometry

set_option autoImplicit false

/-!
# Native finite-field Frobenius endomorphism

Package the existing q-power group map as the original AbVar.End, retaining
q = #k = p^f and the exact original group scheme. This supplies an F-shaped
component, not the actual reduction or Galois comparison required by C10.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Frobenius

namespace C10Frobenius.NativeFiniteField

variable {k : Type} [Field k] [Fintype k] (p f : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ f)

/-- q-power Frobenius in the original endomorphism ring of the given abelian variety. -/
def endomorphism (A : PkgI3.AbVar k) : PkgI3.AbVar.End A :=
  ObjBridge.homOfGrp (FiniteField.endomorphism p f hcard (ObjBridge.toGrp A))

/-- The native endomorphism retains exactly the upstream q-power geometric map. -/
@[simp] theorem endomorphism_hom (A : PkgI3.AbVar k) :
    PkgI3.AbVar.Hom.hom (endomorphism p f hcard A) =
      geometricFrobenius A.X p f hcard :=
  FiniteField.endomorphism_hom p f hcard (ObjBridge.toGrp A)

/-- The same native finite-field Frobenius satisfies the original isogeny predicate. -/
theorem endomorphism_isIsogeny (A : PkgI3.AbVar k) :
    PkgI3.AbVar.IsIsogenyMor (PkgI3.AbVar.Hom.hom (endomorphism p f hcard A)) := by
  let : IsProper A.X.hom := A.proper
  exact Geometry.endomorphism_finiteSurjective_of_proper p f hcard (ObjBridge.toGrp A)

end C10Frobenius.NativeFiniteField
