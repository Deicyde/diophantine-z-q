import ZInQKernel.Contrib.T28.Mestre
import ZInQKernel.Contrib.T28.Special
-- Independent check (task igusa-generic): the two halves close T28.
example : PkgI1.IgusaClebschSeparation :=
  T28.igusaClebschSeparation_of_bothSpecial T28Special.separationBothSpecial
theorem t28_check : PkgI1.IgusaClebschSeparation :=
  T28.igusaClebschSeparation_of_bothSpecial T28Special.separationBothSpecial
#print axioms t28_check
