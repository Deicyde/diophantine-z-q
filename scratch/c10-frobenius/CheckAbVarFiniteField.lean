import C10AbVarFiniteField
import C10PrimeField

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Frobenius

variable {k : Type} [Field k] [Fintype k] (p f : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ f) (A : PkgI3.AbVar k)

-- An actual element of the original native End ring, without a requested conclusion as premise.
example : PkgI3.AbVar.End A := C10Frobenius.NativeFiniteField.endomorphism p f hcard A

example : PkgI3.AbVar.IsIsogenyMor
    (PkgI3.AbVar.Hom.hom (C10Frobenius.NativeFiniteField.endomorphism p f hcard A)) :=
  C10Frobenius.NativeFiniteField.endomorphism_isIsogeny p f hcard A

-- The original scheme and exponent are retained; this is q-power, not p-power over arbitrary k.
example : PkgI3.AbVar.Hom.hom (C10Frobenius.NativeFiniteField.endomorphism p f hcard A) =
    geometricFrobenius A.X p f hcard :=
  C10Frobenius.NativeFiniteField.endomorphism_hom p f hcard A

example (s : Γ(A.X.left, ⊤)) :
    (PkgI3.AbVar.Hom.hom
      (C10Frobenius.NativeFiniteField.endomorphism p f hcard A)).left.appTop s =
        s ^ Fintype.card k :=
  C10Frobenius.FiniteField.endomorphism_appTop p f hcard (ObjBridge.toGrp A) s

-- On the prime field, the native element is the same previously verified geometric map.
example (r : ℕ) [Fact r.Prime] (B : PkgI3.AbVar (ZMod r)) :
    PkgI3.AbVar.Hom.hom (C10Frobenius.NativeFiniteField.endomorphism r 1 (by simp) B) =
      (C10Frobenius.PrimeField.endomorphism r (ObjBridge.toGrp B)).hom.hom := by
  rw [C10Frobenius.NativeFiniteField.endomorphism_hom,
    C10Frobenius.PrimeField.endomorphism_hom_eq_geometricFrobenius]

#check @C10Frobenius.NativeFiniteField.endomorphism
#check @C10Frobenius.NativeFiniteField.endomorphism_hom
#check @C10Frobenius.NativeFiniteField.endomorphism_isIsogeny

#print axioms C10Frobenius.NativeFiniteField.endomorphism
#print axioms C10Frobenius.NativeFiniteField.endomorphism_hom
#print axioms C10Frobenius.NativeFiniteField.endomorphism_isIsogeny
