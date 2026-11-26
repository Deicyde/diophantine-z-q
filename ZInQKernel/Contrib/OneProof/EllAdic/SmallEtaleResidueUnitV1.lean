import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleConstantComparisonV1
import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleResidueSheafV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite

namespace RC53.EllAdic

universe u

private theorem toSheafify_comp_sheafComparison {C D : Type*} [Category* C] [Category* D]
    (J : GrothendieckTopology C) [HasWeakSheafify J D] {P : Cᵒᵖ ⥤ D}
    (F : Sheaf J D) (δ : P ⟶ F.obj) :
    toSheafify J P ≫
      ((presheafToSheaf J D).map δ ≫ (sheafificationNatIso J D).inv.app F).hom = δ := by
  let q := (sheafificationNatIso J D).inv.app F
  have h₁ : δ ≫ toSheafify J F.obj = toSheafify J P ≫ sheafifyMap J δ :=
    toSheafify_naturality J δ
  have h₂ : toSheafify J F.obj ≫ q.hom = 𝟙 F.obj := (isoSheafify J F.property).hom_inv_id
  change toSheafify J P ≫ sheafifyMap J δ ≫ q.hom = δ
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t : P ⟶ sheafify J F.obj => t ≫ q.hom) h₁.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t : F.obj ⟶ F.obj => δ ≫ t) h₂).trans (Category.comp_id δ))))

/-- The pulled-back finite constant sheaf is compared to the literal
pro-étale residue sheaf through the constant comparison. -/
noncomputable def smallEtalePulledResidueIso (S : Scheme.{u}) (p n : ℕ) :
    (smallEtaleAbPullback S).obj
        ((constantSheaf S.smallEtaleTopology Ab.{u+1}).obj (liftedResidueCoefficient.{u} p n)) ≅
      (liftedFiniteResidueProEtSheafTower S p).obj (op n) :=
  (smallEtaleConstantComparison S).app (liftedResidueCoefficient.{u} p n) ≪≫
    liftedResidueConstantSheafIso S p n

/-- The transpose of the specified residue comparison is precisely the
étale sheafification of the literal constant diagonal. -/
theorem smallEtalePulledResidueIso_transpose (S : Scheme.{u}) (p n : ℕ) :
    ((smallEtaleAbAdjunction S).homEquiv
      ((constantSheaf S.smallEtaleTopology Ab.{u+1}).obj (liftedResidueCoefficient.{u} p n))
      ((liftedFiniteResidueProEtSheafTower S p).obj (op n)) (smallEtalePulledResidueIso S p n).hom) =
      (smallEtaleResidueSheafIso S p n).hom := by
  let J := S.smallEtaleTopology
  let K := Scheme.ProEt.topology S
  let M := liftedResidueCoefficient.{u} p n
  let A := (constantSheaf J Ab.{u+1}).obj M
  let B := (constantSheaf K Ab.{u+1}).obj M
  let F := (liftedFiniteResidueProEtSheafTower S p).obj (op n)
  let a := (smallEtaleConstantComparison S).hom.app M
  let b := (liftedResidueConstantSheafIso S p n).hom
  let G := smallEtaleAbPushforward S
  let adj := smallEtaleAbAdjunction S
  let Fₑ := G.obj F
  have h₀ : (adj.homEquiv A F) (a ≫ b) = (adj.homEquiv A B) a ≫ G.map b :=
    adj.homEquiv_naturality_right a b
  change (adj.homEquiv A F) (a ≫ b) = _
  refine h₀.trans ?_
  apply Sheaf.hom_ext
  have hab := smallEtaleConstantComparison_transpose S M
  have hb : toSheafify K ((Functor.const (S.ProEt)ᵒᵖ).obj M) ≫ b.hom =
      liftedResidueConstantDiagonal S p n :=
    toSheafify_comp_sheafComparison K F (liftedResidueConstantDiagonal S p n)
  have hbe : smallEtaleRestrictedConstantUnit S M ≫ (G.map b).hom = smallEtaleResidueDiagonal S p n :=
    congrArg (fun k => Functor.whiskerLeft (smallEtaleToProEt S).op k) hb
  have he : toSheafify J ((Functor.const (S.Etale)ᵒᵖ).obj M) ≫
      (smallEtaleResidueSheafIso S p n).hom.hom = smallEtaleResidueDiagonal S p n :=
    toSheafify_comp_sheafComparison J Fₑ (smallEtaleResidueDiagonal S p n)
  change ((adj.homEquiv A B) a).hom ≫ (G.map b).hom = (smallEtaleResidueSheafIso S p n).hom.hom
  refine (congrArg (fun t => t ≫ (G.map b).hom) hab).trans ?_
  refine (sheafifyLift_comp J (smallEtaleRestrictedConstantUnit S M) (G.obj B).property
    (G.map b).hom Fₑ.property).symm.trans ?_
  exact sheafifyLift_unique J _ Fₑ.property _ (he.trans hbe.symm) |>.symm

/-- The unit itself, for the actual pair of sites and literal finite
coefficient; no unit isomorphism is an input. -/
theorem smallEtaleResidue_unit_isIso (S : Scheme.{u}) (p n : ℕ) :
    IsIso ((smallEtaleAbAdjunction S).unit.app
      ((constantSheaf S.smallEtaleTopology Ab.{u+1}).obj (liftedResidueCoefficient.{u} p n))) := by
  let A := (constantSheaf S.smallEtaleTopology Ab.{u+1}).obj (liftedResidueCoefficient.{u} p n)
  let adj := smallEtaleAbAdjunction S
  let G := smallEtaleAbPushforward S
  let e := smallEtalePulledResidueIso S p n
  have hunit : (adj.homEquiv A ((liftedFiniteResidueProEtSheafTower S p).obj (op n))) e.hom =
      adj.unit.app A ≫ G.map e.hom := rfl
  have hu : adj.unit.app A ≫ G.map e.hom = (smallEtaleResidueSheafIso S p n).hom :=
    hunit.symm.trans (smallEtalePulledResidueIso_transpose S p n)
  let d := G.mapIso e
  have hd : adj.unit.app A = ((smallEtaleResidueSheafIso S p n) ≪≫ d.symm).hom := by
    change adj.unit.app A = (smallEtaleResidueSheafIso S p n).hom ≫ d.inv
    exact (Category.comp_id _).symm.trans
      ((congrArg (fun k => adj.unit.app A ≫ k) d.hom_inv_id.symm).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ d.inv) hu)))
  exact hd.symm ▸ inferInstance

end RC53.EllAdic
