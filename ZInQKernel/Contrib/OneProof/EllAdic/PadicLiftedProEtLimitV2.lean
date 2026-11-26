import ZInQKernel.Contrib.OneProof.EllAdic.PadicResidueSchemeLimitV2
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace RC53.EllAdic

universe u

/-- Restriction to the actual small pro-étale site followed by the same
coefficient universe lift appearing in `Scheme.EllAdicCohomology`. -/
noncomputable def liftedProEtCoefficientPresheaves (S : Scheme.{u}) :
    (Scheme.{u}ᵒᵖ ⥤ Ab.{u}) ⥤ ((S.ProEt)ᵒᵖ ⥤ Ab.{u+1}) :=
  (Functor.whiskeringLeft _ _ _).obj ((Scheme.ProEt.forget S ⋙ Over.forget S).op) ⋙
    (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{u+1,u}

/-- The literal restricted residue diagram, viewed in the coefficient
universe used by the cohomology definition. -/
noncomputable def liftedFiniteResidueProEtTower (S : Scheme.{u}) (p : ℕ) :
    ℕᵒᵖ ⥤ ((S.ProEt)ᵒᵖ ⥤ Ab.{u+1}) :=
  finiteResidueSchemeTower p ⋙ liftedProEtCoefficientPresheaves S

noncomputable def continuousResidueProEtCone (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] :
    Cone (liftedFiniteResidueProEtTower S p) :=
  (liftedProEtCoefficientPresheaves S).mapCone (continuousResidueSchemeCone p)

/-- Whiskering on the left preserves the inverse limit, and whiskering on the
right by the universe lift preserves it as well. Neither step uses an
invariance of derived cohomology under a change of universes. -/
noncomputable def continuousResidueProEtConeIsLimit (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] :
    IsLimit (continuousResidueProEtCone S p) := by
  let : PreservesLimit (finiteResidueSchemeTower.{u} p) (liftedProEtCoefficientPresheaves S) := by
    unfold liftedProEtCoefficientPresheaves
    infer_instance
  exact isLimitOfPreserves (liftedProEtCoefficientPresheaves S) (continuousResidueSchemeConeIsLimit p)

/-- The vertex is exactly the underlying presheaf of the lifted coefficient
sheaf, before the use of `.H`. -/
lemma continuousResidueProEtCone_pt (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] :
    (continuousResidueProEtCone S p).pt =
      ((sheafCompose (Scheme.ProEt.topology S) AddCommGrpCat.uliftFunctor.{u+1}).obj
        (S.ellAdicSheaf p)).obj := rfl

end RC53.EllAdic
