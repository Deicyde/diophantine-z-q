import C10Frobenius

set_option autoImplicit false

-- Exact statements and complete transitive axiom dependencies of this adapter.
#check @C10Frobenius.relativeHom
#check @C10Frobenius.relativeHom_hom
#check @C10Frobenius.isMonHom_relativeFrobenius
#check @C10Frobenius.relativeHom_naturality
#check @C10Frobenius.relativeHom_onPoints

#print axioms C10Frobenius.relativeNatTrans
#print axioms C10Frobenius.twistMonoidal
#print axioms C10Frobenius.relativeGroupNatTrans
#print axioms C10Frobenius.groupTwist
#print axioms C10Frobenius.relativeHom
#print axioms C10Frobenius.relativeHom_hom
#print axioms C10Frobenius.isMonHom_relativeFrobenius
#print axioms C10Frobenius.relativeHom_naturality
#print axioms C10Frobenius.relativeHom_onPoints
