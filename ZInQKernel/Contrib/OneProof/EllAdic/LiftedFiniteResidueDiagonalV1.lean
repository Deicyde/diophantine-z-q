import ZInQKernel.Contrib.OneProof.EllAdic.PadicLiftedProEtLimitV2

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite

namespace RC53.EllAdic

universe u

/-- The ordinary finite residue group placed in the coefficient universe
used by `Scheme.EllAdicCohomology`. -/
def liftedResidueCoefficient (p n : ℕ) : Ab.{u+1} :=
  AddCommGrpCat.of (ULift.{u+1} (ZMod (p ^ n)))

/-- The diagonal from the constant presheaf to the literal lifted,
locally constant residue presheaf on the small pro-étale site. -/
noncomputable def liftedResidueConstantDiagonal (S : Scheme.{u}) (p n : ℕ) :
    (Functor.const ((S.ProEt)ᵒᵖ)).obj (liftedResidueCoefficient.{u} p n) ⟶
      (liftedFiniteResidueProEtTower S p).obj (op n) where
  app U := AddCommGrpCat.ofHom {
    toFun := fun a => ⟨LocallyConstant.const _ a.down⟩
    map_zero' := rfl
    map_add' _ _ := rfl }
  naturality _ _ _ := by
    apply AddCommGrpCat.hom_ext
    apply DFunLike.ext
    intro a
    rfl

/-- Reduction on the lifted finite coefficient objects. -/
def liftedResidueCoefficientTransition (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    liftedResidueCoefficient.{u} p n ⟶ liftedResidueCoefficient.{u} p m :=
  AddCommGrpCat.ofHom {
    toFun := fun a => ⟨padicResidueProjection p h a.down⟩
    map_zero' := congrArg ULift.up (map_zero (padicResidueProjection p h))
    map_add' a b := congrArg ULift.up (map_add (padicResidueProjection p h) a.down b.down) }

/-- The constant diagonal compares the very same reduction arrows; neither
finite coefficient system changes when the diagonal is applied. -/
lemma liftedResidueConstantDiagonal_reduction (S : Scheme.{u}) (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    liftedResidueConstantDiagonal S p n ≫ (liftedFiniteResidueProEtTower S p).map (homOfLE h).op =
      (Functor.const ((S.ProEt)ᵒᵖ)).map (liftedResidueCoefficientTransition.{u} p h) ≫
        liftedResidueConstantDiagonal S p m := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply DFunLike.ext
  intro a
  rfl

end RC53.EllAdic
