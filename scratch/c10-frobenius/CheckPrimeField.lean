import C10PrimeField

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Frobenius

-- Public API checks use the original group objects, with no assumed homomorphism property.
example (p : ℕ) [Fact p.Prime] (A : Grp (Over (Spec (.of (ZMod p))))) : A ⟶ A :=
  C10Frobenius.PrimeField.endomorphism p A

example (p : ℕ) [Fact p.Prime] (A : Grp (Over (Spec (.of (ZMod p))))) :
    IsMonHom (geometricFrobenius A.X p 1 (by simp)) :=
  C10Frobenius.PrimeField.isMonHom_geometricFrobenius p A

#check @C10Frobenius.PrimeField.groupTwistIso
#check @C10Frobenius.PrimeField.endomorphism
#check @C10Frobenius.PrimeField.endomorphism_hom_eq_geometricFrobenius
#check @C10Frobenius.PrimeField.isMonHom_geometricFrobenius
#check @C10Frobenius.PrimeField.endomorphism_naturality
#check @C10Frobenius.PrimeField.endomorphism_onPoints

#print axioms C10Frobenius.PrimeField.baseFrobenius_eq_id
#print axioms C10Frobenius.PrimeField.twistIso
#print axioms C10Frobenius.PrimeField.twistIso_hom_left
#print axioms C10Frobenius.PrimeField.groupTwistIso
#print axioms C10Frobenius.PrimeField.groupTwistIso_hom_left
#print axioms C10Frobenius.PrimeField.endomorphism
#print axioms C10Frobenius.PrimeField.endomorphism_left
#print axioms C10Frobenius.PrimeField.endomorphism_hom_eq_geometricFrobenius
#print axioms C10Frobenius.PrimeField.isMonHom_geometricFrobenius
#print axioms C10Frobenius.PrimeField.endomorphism_naturality
#print axioms C10Frobenius.PrimeField.endomorphism_onPoints
