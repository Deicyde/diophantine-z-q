import C10FrobeniusGeometry

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

variable {k : Type} [Field k] [Fintype k] (p f : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ f) (A : Grp (Over (Spec (.of k))))

-- Scheme-level surjectivity holds for the exact original map, without point-surjectivity data.
example : Surjective (C10Frobenius.FiniteField.endomorphism p f hcard A).hom.hom.left :=
  C10Frobenius.Geometry.endomorphism_surjective p f hcard A

-- Finiteness retains local finite type on the original group scheme.
example [LocallyOfFiniteType A.X.hom] :
    IsFinite (C10Frobenius.FiniteField.endomorphism p f hcard A).hom.hom.left :=
  C10Frobenius.Geometry.endomorphism_isFinite p f hcard A

-- Properness, already a field of an abelian-variety object, supplies local finite type.
example [IsProper A.X.hom] :
    IsFinite (C10Frobenius.FiniteField.endomorphism p f hcard A).hom.hom.left ∧
      Surjective (C10Frobenius.FiniteField.endomorphism p f hcard A).hom.hom.left :=
  C10Frobenius.Geometry.endomorphism_finiteSurjective_of_proper p f hcard A

#check @C10Frobenius.Geometry.absolutePower_universalHomeomorphism
#check @C10Frobenius.Geometry.endomorphism_universalHomeomorphism
#check @C10Frobenius.Geometry.endomorphism_surjective
#check @C10Frobenius.Geometry.endomorphism_isFinite
#check @C10Frobenius.Geometry.endomorphism_finiteSurjective_of_proper

#print axioms C10Frobenius.Geometry.absolutePower_universalHomeomorphism
#print axioms C10Frobenius.Geometry.endomorphism_universalHomeomorphism
#print axioms C10Frobenius.Geometry.endomorphism_surjective
#print axioms C10Frobenius.Geometry.endomorphism_isFinite
#print axioms C10Frobenius.Geometry.endomorphism_finiteSurjective_of_proper
