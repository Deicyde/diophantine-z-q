import C10FiniteField
import C10PrimeField

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Frobenius

-- Check the actual group-object API uniformly, not by assuming IsMonHom.
example {k : Type} [Field k] [Fintype k] (p f : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ f) (A : Grp (Over (Spec (.of k)))) : A ⟶ A :=
  C10Frobenius.FiniteField.endomorphism p f hcard A

example {k : Type} [Field k] [Fintype k] (p f : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ f) (A : Grp (Over (Spec (.of k)))) :
    IsMonHom (geometricFrobenius A.X p f hcard) :=
  C10Frobenius.FiniteField.isMonHom_geometricFrobenius p f hcard A

-- Both adapters agree on the prime field because they package the same upstream map.
example (p : ℕ) [Fact p.Prime] (A : Grp (Over (Spec (.of (ZMod p))))) :
    C10Frobenius.FiniteField.endomorphism p 1 (by simp) A =
      C10Frobenius.PrimeField.endomorphism p A := by
  apply Grp.hom_ext
  rw [C10Frobenius.FiniteField.endomorphism_hom,
    C10Frobenius.PrimeField.endomorphism_hom_eq_geometricFrobenius]

#check @C10Frobenius.FiniteField.endomorphism
#check @C10Frobenius.FiniteField.endomorphism_hom
#check @C10Frobenius.FiniteField.isMonHom_geometricFrobenius
#check @C10Frobenius.FiniteField.endomorphism_naturality
#check @C10Frobenius.FiniteField.endomorphism_onPoints
#check @C10Frobenius.FiniteField.endomorphism_appTop

#print axioms C10Frobenius.FiniteField.geometric_naturality
#print axioms C10Frobenius.FiniteField.geometricNatTrans
#print axioms C10Frobenius.FiniteField.geometricGroupNatTrans
#print axioms C10Frobenius.FiniteField.endomorphism
#print axioms C10Frobenius.FiniteField.endomorphism_hom
#print axioms C10Frobenius.FiniteField.isMonHom_geometricFrobenius
#print axioms C10Frobenius.FiniteField.endomorphism_naturality
#print axioms C10Frobenius.FiniteField.endomorphism_onPoints
#print axioms C10Frobenius.FiniteField.endomorphism_appTop
