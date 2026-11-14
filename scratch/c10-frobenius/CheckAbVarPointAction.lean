import C10AbVarPointAction

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

local instance coefficientFivePrime : Fact (Nat.Prime 5) := ⟨by norm_num⟩

variable {k : Type} [Field k] [Fintype k] (p f : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ f) (A : PkgI3.AbVar k)

-- The original native point-homomorphism equality, with the extension hypotheses explicit.
example (K : Type) [Field K] [Algebra k K] [CharP K p] [PerfectRing K p] :
    PkgI3.AbVar.ptMap (L := K) (C10Frobenius.NativeFiniteField.endomorphism p f hcard A) =
      A.galAct (Stacks.Frobenius.arithmeticFrobenius k K p f hcard) :=
  C10Frobenius.NativePointAction.ptMap_eq_galAct K p f hcard A

-- Every coefficient prime uses the same original native module and arithmetic element.
example (ℓ : ℕ) [Fact ℓ.Prime] :
    PkgI3.AbVar.homT (ℓ := ℓ) (C10Frobenius.NativeFiniteField.endomorphism p f hcard A) =
      A.galT (ℓ := ℓ) (C10Frobenius.NativePointAction.arithmeticGal p f hcard) :=
  C10Frobenius.NativePointAction.homT_eq_galT p f hcard A ℓ

-- Both 3 and 5 retain the SAME A, finite field, q-power endomorphism and Galois element.
example :
    (PkgI3.AbVar.homT (ℓ := 3)
      (C10Frobenius.NativeFiniteField.endomorphism p f hcard A)).baseChange ℚ_[3] =
        A.galRep 3 (C10Frobenius.NativePointAction.arithmeticGal p f hcard) ∧
    (PkgI3.AbVar.homT (ℓ := 5)
      (C10Frobenius.NativeFiniteField.endomorphism p f hcard A)).baseChange ℚ_[5] =
        A.galRep 5 (C10Frobenius.NativePointAction.arithmeticGal p f hcard) :=
  ⟨C10Frobenius.NativePointAction.homT_baseChange_eq_galRep p f hcard A 3,
    C10Frobenius.NativePointAction.homT_baseChange_eq_galRep p f hcard A 5⟩

example (x : AlgebraicClosure k) :
    (AlgEquiv.toAlgHom (C10Frobenius.NativePointAction.arithmeticGal p f hcard)) x =
      x ^ Fintype.card k :=
  C10Frobenius.NativePointAction.arithmeticGal_apply p f hcard x

#check @C10Frobenius.NativePointAction.ptMap_apply
#check @C10Frobenius.NativePointAction.ptMap_eq_galAct
#check @C10Frobenius.NativePointAction.arithmeticGal
#check @C10Frobenius.NativePointAction.arithmeticGal_apply
#check @C10Frobenius.NativePointAction.ptMap_eq_galAct_arithmeticGal
#check @C10Frobenius.NativePointAction.homT_eq_galT
#check @C10Frobenius.NativePointAction.homT_baseChange_eq_galRep

#print axioms C10Frobenius.NativePointAction.ptMap_apply
#print axioms C10Frobenius.NativePointAction.ptMap_eq_galAct
#print axioms C10Frobenius.NativePointAction.arithmeticGal
#print axioms C10Frobenius.NativePointAction.arithmeticGal_apply
#print axioms C10Frobenius.NativePointAction.ptMap_eq_galAct_arithmeticGal
#print axioms C10Frobenius.NativePointAction.homT_eq_galT
#print axioms C10Frobenius.NativePointAction.homT_baseChange_eq_galRep
#print axioms coefficientFivePrime
