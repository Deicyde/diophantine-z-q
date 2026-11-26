import ZInQKernel.Contrib.OneProof.EllAdic.LiftedFiniteResidueIsSheafV1
import Mathlib.CategoryTheory.Sites.Limits

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace RC53.EllAdic

universe u

/-- The actual finite locally constant residue diagram in the category of
sheaves with the same coefficients as in `Scheme.EllAdicCohomology`. -/
noncomputable def liftedFiniteResidueProEtSheafTower (S : Scheme.{u}) (p : ℕ) :
    ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology S) Ab.{u+1} where
  obj n := ⟨(liftedFiniteResidueProEtTower S p).obj n, liftedFiniteResidueProEt_isSheaf S p n.unop⟩
  map f := ⟨(liftedFiniteResidueProEtTower S p).map f⟩
  map_id n := Sheaf.hom_ext ((liftedFiniteResidueProEtTower S p).map_id n)
  map_comp f g := Sheaf.hom_ext ((liftedFiniteResidueProEtTower S p).map_comp f g)

/-- The cone on the finite residue sheaves, with the exact lifted p-adic
coefficient sheaf as its vertex. -/
noncomputable def continuousResidueProEtSheafCone (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] :
    Cone (liftedFiniteResidueProEtSheafTower S p) where
  pt := (sheafCompose (Scheme.ProEt.topology S) AddCommGrpCat.uliftFunctor.{u+1}).obj
    (S.ellAdicSheaf p)
  π := {
    app n := ⟨(continuousResidueProEtCone S p).π.app n⟩
    naturality _ _ f := Sheaf.hom_ext ((continuousResidueProEtCone S p).π.naturality f) }

/-- The sheaf inclusion reflects the limit already constructed with the same
projections in presheaves; this does not assert that cohomology preserves it. -/
noncomputable def continuousResidueProEtSheafConeIsLimit (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] :
    IsLimit (continuousResidueProEtSheafCone S p) :=
  isLimitOfReflects (sheafToPresheaf (Scheme.ProEt.topology S) Ab.{u+1})
    (continuousResidueProEtConeIsLimit S p)

end RC53.EllAdic
