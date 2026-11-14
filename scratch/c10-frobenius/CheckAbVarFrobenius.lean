import C10AbVarFrobenius

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Frobenius

variable {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
  (A : PkgI3.AbVar k)

-- Actual native Hom, without an assumed group-homomorphism or isogeny premise.
example : PkgI3.AbVar.Hom A (C10Frobenius.NativeAbVar.twist p A) :=
  C10Frobenius.NativeAbVar.hom p A

example : PkgI3.AbVar.IsIsogenyMor
    (PkgI3.AbVar.Hom.hom (C10Frobenius.NativeAbVar.hom p A)) :=
  C10Frobenius.NativeAbVar.hom_isIsogeny p A

-- The original group object and original relative Frobenius are unchanged.
example : ObjBridge.toGrp (C10Frobenius.NativeAbVar.twist p A) =
    C10Frobenius.groupTwist (Spec (.of k)) p (isInCharacteristic_spec k p)
      (ObjBridge.toGrp A) :=
  C10Frobenius.NativeAbVar.toGrp_twist p A

example : PkgI3.AbVar.Hom.hom (C10Frobenius.NativeAbVar.hom p A) =
    relativeFrobenius (Spec (.of k)) p (isInCharacteristic_spec k p) A.X :=
  C10Frobenius.NativeAbVar.hom_hom p A

#check @C10Frobenius.NativeAbVar.twistIsAbelianVariety
#check @C10Frobenius.NativeAbVar.twist
#check @C10Frobenius.NativeAbVar.toGrp_twist
#check @C10Frobenius.NativeAbVar.hom
#check @C10Frobenius.NativeAbVar.hom_hom
#check @C10Frobenius.NativeAbVar.hom_isIsogeny

#print axioms C10Frobenius.NativeAbVar.twistIsAbelianVariety
#print axioms C10Frobenius.NativeAbVar.twist
#print axioms C10Frobenius.NativeAbVar.toGrp_twist
#print axioms C10Frobenius.NativeAbVar.hom
#print axioms C10Frobenius.NativeAbVar.hom_hom
#print axioms C10Frobenius.NativeAbVar.hom_isIsogeny
