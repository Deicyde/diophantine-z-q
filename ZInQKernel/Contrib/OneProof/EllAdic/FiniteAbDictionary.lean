import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

namespace RC53.EllAdic.FiniteAbDictionary

universe u

scoped instance etaleSheafify (S : Scheme.{u}) :
    HasSheafify S.smallEtaleTopology Ab.{u+1} := inferInstance

scoped instance proEtSheafify (S : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology S) Ab.{u+1} := inferInstance

private theorem etaleGroth (S : Scheme.{u}) :
    IsGrothendieckAbelian.{u+1} (Sheaf S.smallEtaleTopology Ab.{u+1}) := by
  let : EssentiallySmall.{u+1} S.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall S.smallEtaleTopology Ab.{u+1}

private theorem proEtGroth (S : Scheme.{u}) :
    IsGrothendieckAbelian.{u+1} (Sheaf (Scheme.ProEt.topology S) Ab.{u+1}) := by
  let : EssentiallySmall.{u+1} S.ProEt := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall (Scheme.ProEt.topology S) Ab.{u+1}

scoped instance etaleExt (S : Scheme.{u}) :
    HasExt.{u+1} (Sheaf S.smallEtaleTopology Ab.{u+1}) := by
  let := etaleGroth S
  exact IsGrothendieckAbelian.hasExt (Sheaf S.smallEtaleTopology Ab.{u+1})

scoped instance proEtExt (S : Scheme.{u}) :
    HasExt.{u+1} (Sheaf (Scheme.ProEt.topology S) Ab.{u+1}) := by
  let := proEtGroth S
  exact IsGrothendieckAbelian.hasExt (Sheaf (Scheme.ProEt.topology S) Ab.{u+1})

abbrev zCoeff : Ab.{u+1} := AddCommGrpCat.of (ULift.{u+1} ℤ)

end RC53.EllAdic.FiniteAbDictionary
