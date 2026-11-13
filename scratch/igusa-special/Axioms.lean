import ZInQKernel.Contrib.T28.Assemble
#print axioms T28.igusaClebschSeparation_proved
#print axioms T28.igusaSeparationEq_proved
#print axioms T28.separationSpecial_proved
#print axioms T28Special.separationBothSpecial
#print axioms T28Special.special_to_E
#print axioms T28Special.special_Nr
#print axioms T28Special.det_yv_Nr
#print axioms T28Special.exists_Nr
#print axioms T28Special.E_sep
#print axioms T28Special.fam_alg
#print axioms T28Special.E_D4
#print axioms T28Special.even_to_E
example : T28Special.separationBothSpecial = T28Special.separationBothSpecial := rfl
example : T28.SeparationBothSpecial := T28Special.separationBothSpecial
example : PkgI1.IgusaClebschSeparation := T28.igusaClebschSeparation_proved
