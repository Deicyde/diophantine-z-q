import C10FieldPoints
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Frobenius
open scoped CategoryTheory.MonObj

-- Compare the actual point maps, without assuming the desired equality or bijectivity.
example {k K : Type} [Field k] [Fintype k] [Field K] [Algebra k K]
    (p f : ℕ) [Fact p.Prime] [CharP k p] [CharP K p] [PerfectRing K p]
    (hcard : Fintype.card k = p ^ f) (A : Grp (Over (Spec (.of k))))
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.X) :
    x ≫ (C10Frobenius.FiniteField.endomorphism p f hcard A).hom.hom =
      C10Frobenius.FieldPoints.arithmeticPointEquiv K p f hcard A x :=
  C10Frobenius.FieldPoints.endomorphism_eq_arithmeticPointEquiv K p f hcard A x

-- An algebraically closed extension supplies perfectness; its characteristic is inherited.
example {k K : Type} [Field k] [Fintype k] [Field K] [Algebra k K] [IsAlgClosed K]
    (p f : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ f)
    (A : Grp (Over (Spec (.of k)))) :
    Function.Bijective (fun x :
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.X =>
        x ≫ (C10Frobenius.FiniteField.endomorphism p f hcard A).hom.hom) := by
  let : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  exact C10Frobenius.FieldPoints.endomorphism_bijective_onFieldPoints K p f hcard A

#check @C10Frobenius.FieldPoints.arithmeticFrobenius_specMap
#check @C10Frobenius.FieldPoints.endomorphism_onFieldPoints
#check @C10Frobenius.FieldPoints.arithmeticPointEquiv
#check @C10Frobenius.FieldPoints.endomorphism_eq_arithmeticPointEquiv
#check @C10Frobenius.FieldPoints.endomorphism_bijective_onFieldPoints

#print axioms C10Frobenius.FieldPoints.arithmeticFrobenius_specMap
#print axioms C10Frobenius.FieldPoints.endomorphism_onFieldPoints
#print axioms C10Frobenius.FieldPoints.fieldAutomorphismIso
#print axioms C10Frobenius.FieldPoints.arithmeticPointEquiv
#print axioms C10Frobenius.FieldPoints.arithmeticPointEquiv_apply
#print axioms C10Frobenius.FieldPoints.endomorphism_eq_arithmeticPointEquiv
#print axioms C10Frobenius.FieldPoints.endomorphism_bijective_onFieldPoints
