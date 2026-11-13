import C10TorsionAction

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

variable {k K : Type} [Field k] [Fintype k] [Field K] [Algebra k K]
  (p f : ℕ) [Fact p.Prime] [CharP k p] [CharP K p] [PerfectRing K p]
  (hcard : Fintype.card k = p ^ f) (A : Grp (Over (Spec (.of k))))

-- All orders are retained; the action is the actual scheme Frobenius on the same point group.
example (n : ℕ) :
    Set.BijOn (fun x :
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.X =>
        x ≫ (C10Frobenius.FiniteField.endomorphism p f hcard A).hom.hom)
      {x | x ^ n = 1} {x | x ^ n = 1} :=
  C10Frobenius.TorsionAction.endomorphism_bijOn_nTorsion K p f hcard A n

-- This checks every prime-power level parametrically, without choosing one coefficient prime.
example (ℓ m : ℕ) :
    {x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.X // x ^ (ℓ ^ m) = 1} ≃
      {x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.X // x ^ (ℓ ^ m) = 1} :=
  C10Frobenius.TorsionAction.torsionPointEquiv K p f hcard A (ℓ ^ m)

-- The zero-order predicate is the whole point set; its actual action is unchanged.
example (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.X) :
    (C10Frobenius.TorsionAction.torsionPointEquiv K p f hcard A 0 ⟨x, by simp⟩).val =
      x ≫ (C10Frobenius.FiniteField.endomorphism p f hcard A).hom.hom :=
  C10Frobenius.TorsionAction.torsionPointEquiv_apply K p f hcard A 0 _

#check @C10Frobenius.TorsionAction.endomorphism_pow_eq_one_iff
#check @C10Frobenius.TorsionAction.endomorphism_bijOn_nTorsion
#check @C10Frobenius.TorsionAction.torsionPointEquiv
#check @C10Frobenius.TorsionAction.torsionPointEquiv_apply

#print axioms C10Frobenius.TorsionAction.endomorphism_pow_eq_one_iff
#print axioms C10Frobenius.TorsionAction.endomorphism_bijOn_nTorsion
#print axioms C10Frobenius.TorsionAction.torsionPointEquiv
#print axioms C10Frobenius.TorsionAction.torsionPointEquiv_apply
