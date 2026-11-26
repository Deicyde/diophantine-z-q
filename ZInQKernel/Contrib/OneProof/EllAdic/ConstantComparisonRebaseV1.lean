import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleProEtNormalizedMateV1
import ZInQKernel.Contrib.OneProof.EllAdic.ConstantSheafTransport
import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleConstantComparisonV1
import ZInQKernel.Contrib.OneProof.EllAdic.LiftedFiniteResidueConstantSheafV1
import ZInQKernel.Contrib.OneProof.EllAdic.PadicProEtCoefficientRebaseV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite

namespace RC53.EllAdic

universe u

local instance constantRebaseEtaleForward {S T : Scheme.{u}} (σ : S ≅ T) :
    (smallEtaleRebaseEquivalence σ).functor.IsContinuous S.smallEtaleTopology T.smallEtaleTopology :=
  smallEtaleRebaseIso_isContinuous σ

local instance constantRebaseEtaleInverse {S T : Scheme.{u}} (σ : S ≅ T) :
    (smallEtaleRebaseEquivalence σ).inverse.IsContinuous T.smallEtaleTopology S.smallEtaleTopology :=
  smallEtaleRebaseIso_isContinuous σ.symm

local instance constantRebaseProEtForward {S T : Scheme.{u}} (σ : S ≅ T) :
    (smallProEtRebaseEquivalence σ).functor.IsContinuous (Scheme.ProEt.topology S) (Scheme.ProEt.topology T) :=
  smallProEtRebaseIso_isContinuous σ

local instance constantRebaseProEtInverse {S T : Scheme.{u}} (σ : S ≅ T) :
    (smallProEtRebaseEquivalence σ).inverse.IsContinuous (Scheme.ProEt.topology T) (Scheme.ProEt.topology S) :=
  smallProEtRebaseIso_isContinuous σ.symm

/-- Rebase the actual small étale constant sheaf by its literal sheafification unit. -/
noncomputable def etaleConstantRebaseIso {S T : Scheme.{u}} (σ : S ≅ T) :
    constantSheaf S.smallEtaleTopology Ab.{u+1} ≅
      constantSheaf T.smallEtaleTopology Ab.{u+1} ⋙ etaleAbRebasePullback σ :=
  ConstantSheafTransport.k (smallEtaleRebaseEquivalence σ) S.smallEtaleTopology T.smallEtaleTopology Ab.{u+1}

/-- Rebase the actual small pro-étale constant sheaf by the same construction. -/
noncomputable def proEtConstantRebaseIso {S T : Scheme.{u}} (σ : S ≅ T) :
    constantSheaf (Scheme.ProEt.topology S) Ab.{u+1} ≅
      constantSheaf (Scheme.ProEt.topology T) Ab.{u+1} ⋙ proEtAbRebasePullback σ :=
  ConstantSheafTransport.k (smallProEtRebaseEquivalence σ)
    (Scheme.ProEt.topology S) (Scheme.ProEt.topology T) Ab.{u+1}

private theorem etaleConstantRebaseIso_unit {S T : Scheme.{u}} (σ : S ≅ T) (M : Ab.{u+1}) :
    toSheafify S.smallEtaleTopology ((Functor.const (S.Etale)ᵒᵖ).obj M) ≫
      ((etaleConstantRebaseIso σ).hom.app M).hom =
    Functor.whiskerLeft (smallEtaleRebaseIso σ).op
      (toSheafify T.smallEtaleTopology ((Functor.const (T.Etale)ᵒᵖ).obj M)) :=
  ConstantSheafTransport.k_toSheafify (smallEtaleRebaseEquivalence σ)
    S.smallEtaleTopology T.smallEtaleTopology Ab.{u+1} M

private theorem proEtConstantRebaseIso_unit {S T : Scheme.{u}} (σ : S ≅ T) (M : Ab.{u+1}) :
    toSheafify (Scheme.ProEt.topology S) ((Functor.const (S.ProEt)ᵒᵖ).obj M) ≫
      ((proEtConstantRebaseIso σ).hom.app M).hom =
    Functor.whiskerLeft (smallProEtRebaseIso σ).op
      (toSheafify (Scheme.ProEt.topology T) ((Functor.const (T.ProEt)ᵒᵖ).obj M)) :=
  ConstantSheafTransport.k_toSheafify (smallProEtRebaseEquivalence σ)
    (Scheme.ProEt.topology S) (Scheme.ProEt.topology T) Ab.{u+1} M

private theorem smallEtaleConstantComparison_unit_transpose (S : Scheme.{u}) (M : Ab.{u+1}) :
    toSheafify S.smallEtaleTopology ((Functor.const (S.Etale)ᵒᵖ).obj M) ≫
      (((smallEtaleAbAdjunction S).homEquiv _ _ ((smallEtaleConstantComparison S).hom.app M))).hom =
      smallEtaleRestrictedConstantUnit S M := by
  rw [smallEtaleConstantComparison_transpose]
  exact toSheafify_sheafifyLift _ _ _

/-- The canonical constant comparison respects rebase, with the normalized
mate of the actual restriction square and the literal sheafification units. -/
theorem smallEtaleConstantComparison_rebase {S T : Scheme.{u}} (σ : S ≅ T) (M : Ab.{u+1}) :
    (smallEtaleAbPullback S).map ((etaleConstantRebaseIso σ).hom.app M) ≫
      (smallEtaleRebaseNormalizedMate σ).hom.app ((constantSheaf T.smallEtaleTopology Ab.{u+1}).obj M) ≫
        (proEtAbRebasePullback σ).map ((smallEtaleConstantComparison T).hom.app M) =
    (smallEtaleConstantComparison S).hom.app M ≫ (proEtConstantRebaseIso σ).hom.app M := by
  let A := smallEtaleAbAdjunction S
  let B := smallEtaleAbAdjunction T
  let E := etaleAbRebasePullback σ
  let G := smallEtaleAbPushforward S
  let kE := (etaleConstantRebaseIso σ).hom.app M
  let kP := (proEtConstantRebaseIso σ).hom.app M
  let cS := (smallEtaleConstantComparison S).hom.app M
  let cT := (smallEtaleConstantComparison T).hom.app M
  let Q := (rebaseDirectImageSquare σ).inv.app ((constantSheaf (Scheme.ProEt.topology T) Ab.{u+1}).obj M)
  let X := (constantSheaf T.smallEtaleTopology Ab.{u+1}).obj M
  let Y := (constantSheaf (Scheme.ProEt.topology T) Ab.{u+1}).obj M
  let V := proEtAbRebasePullback σ
  let a := (smallEtaleRebaseNormalizedMate σ).hom.app X
  have left := A.homEquiv_naturality_left kE (a ≫ V.map cT)
  have mid := smallEtaleRebaseNormalizedMate_transpose σ X Y cT
  have right := A.homEquiv_naturality_right cS kP
  apply (A.homEquiv _ _).injective
  refine left.trans ((congrArg (fun k => kE ≫ k) mid).trans (Eq.trans ?_ right.symm))
  apply Sheaf.hom_ext
  apply sheafify_hom_ext S.smallEtaleTopology _ _ (G.obj (V.obj Y)).property
  let η := toSheafify S.smallEtaleTopology ((Functor.const (S.Etale)ᵒᵖ).obj M)
  let uT := (B.homEquiv X Y) cT
  let uS := A.homEquiv _ _ cS
  let kEh : sheafify S.smallEtaleTopology ((Functor.const (S.Etale)ᵒᵖ).obj M) ⟶ (E.obj X).obj := kE.hom
  let uSh : sheafify S.smallEtaleTopology ((Functor.const (S.Etale)ᵒᵖ).obj M) ⟶ _ := uS.hom
  let t := (E.map uT).hom
  let k := (G.map kP).hom
  change η ≫ (kEh ≫ t ≫ Q.hom) = η ≫ (uSh ≫ k)
  let Wₑ := (Functor.whiskeringLeft (S.Etale)ᵒᵖ (T.Etale)ᵒᵖ Ab.{u+1}).obj (smallEtaleRebaseIso σ).op
  let Wᵢ := (Functor.whiskeringLeft (S.Etale)ᵒᵖ (S.ProEt)ᵒᵖ Ab.{u+1}).obj (smallEtaleToProEt S).op
  let Wₚ := (Functor.whiskeringLeft (S.ProEt)ᵒᵖ (T.ProEt)ᵒᵖ Ab.{u+1}).obj (smallProEtRebaseIso σ).op
  let ηT := toSheafify T.smallEtaleTopology ((Functor.const (T.Etale)ᵒᵖ).obj M)
  let ηP := toSheafify (Scheme.ProEt.topology T) ((Functor.const (T.ProEt)ᵒᵖ).obj M)
  let g := Wₑ.map (smallEtaleRestrictedConstantUnit T M)
  let h := Wᵢ.map (Wₚ.map ηP)
  have hE : η ≫ kEh = Wₑ.map ηT := etaleConstantRebaseIso_unit σ M
  have h₁ₐ : (η ≫ kEh) ≫ t = Wₑ.map ηT ≫ t := congrArg (fun f => f ≫ t) hE
  have h₁ᵦ : Wₑ.map ηT ≫ t = g :=
    congrArg (fun f => Wₑ.map f) (smallEtaleConstantComparison_unit_transpose T M)
  have h₁ : (η ≫ kEh) ≫ t = g := Eq.trans h₁ₐ h₁ᵦ
  have h₂ₐ : (η ≫ uSh) ≫ k = smallEtaleRestrictedConstantUnit S M ≫ k :=
    congrArg (fun f => f ≫ k) (smallEtaleConstantComparison_unit_transpose S M)
  have h₂ᵦ : smallEtaleRestrictedConstantUnit S M ≫ k = h :=
    congrArg (fun f => Wᵢ.map f) (proEtConstantRebaseIso_unit σ M)
  have h₂ : (η ≫ uSh) ≫ k = h := Eq.trans h₂ₐ h₂ᵦ
  have hm : g ≫ Q.hom = h := Category.comp_id h
  exact Eq.trans (Category.assoc η kEh (t ≫ Q.hom)).symm
    (Eq.trans (Category.assoc (η ≫ kEh) t Q.hom).symm
    (Eq.trans (congrArg (fun f => f ≫ Q.hom) h₁)
    (Eq.trans hm (Eq.trans h₂.symm (Category.assoc η uSh k)))))

private theorem liftedResidueConstantSheafIso_unit (S : Scheme.{u}) (p n : ℕ) :
    toSheafify (Scheme.ProEt.topology S)
      ((Functor.const (S.ProEt)ᵒᵖ).obj (liftedResidueCoefficient.{u} p n)) ≫
        (liftedResidueConstantSheafIso S p n).hom.hom = liftedResidueConstantDiagonal S p n := by
  let J := Scheme.ProEt.topology S
  let F := (liftedFiniteResidueProEtSheafTower S p).obj (op n)
  let P := (Functor.const (S.ProEt)ᵒᵖ).obj (liftedResidueCoefficient.{u} p n)
  let δ : P ⟶ F.obj := liftedResidueConstantDiagonal S p n
  let q : sheafify J F.obj ⟶ F.obj := ((sheafificationNatIso J Ab.{u+1}).inv.app F).hom
  let η := toSheafify J P
  let z := sheafifyMap J δ
  have h : toSheafify J F.obj ≫ q = 𝟙 F.obj := (isoSheafify J F.property).hom_inv_id
  change η ≫ (z ≫ q) = δ
  calc
    _ = (η ≫ z) ≫ q := (Category.assoc η z q).symm
    _ = (δ ≫ toSheafify J F.obj) ≫ q := congrArg (fun f => f ≫ q) (toSheafify_naturality J δ).symm
    _ = δ ≫ (toSheafify J F.obj ≫ q) := Category.assoc δ _ q
    _ = δ ≫ 𝟙 F.obj := congrArg (fun f => δ ≫ f) h
    _ = _ := Category.comp_id δ

/-- The finite constant comparison and the actual locally constant residue
coefficient rebase agree on the diagonal. -/
theorem liftedResidueConstantSheafIso_rebase {S T : Scheme.{u}} (σ : S ≅ T) (p n : ℕ) :
    (proEtConstantRebaseIso σ).hom.app (liftedResidueCoefficient.{u} p n) ≫
      (proEtAbRebasePullback σ).map (liftedResidueConstantSheafIso T p n).hom ≫
        (liftedFiniteResidueProEtRebaseIso σ p n).hom =
    (liftedResidueConstantSheafIso S p n).hom := by
  let J := Scheme.ProEt.topology S
  let M := liftedResidueCoefficient.{u} p n
  let η := toSheafify J ((Functor.const (S.ProEt)ᵒᵖ).obj M)
  let F := (liftedFiniteResidueProEtSheafTower S p).obj (op n)
  let Y := (constantSheaf (Scheme.ProEt.topology T) Ab.{u+1}).obj M
  let V := proEtAbRebasePullback σ
  let k : sheafify J ((Functor.const (S.ProEt)ᵒᵖ).obj M) ⟶ (V.obj Y).obj := ((proEtConstantRebaseIso σ).hom.app M).hom
  let l := (liftedFiniteResidueProEtRebaseIso σ p n).hom.hom
  let b := (liftedResidueConstantSheafIso T p n).hom
  let t := (V.map b).hom
  let δ : (Functor.const (S.ProEt)ᵒᵖ).obj M ⟶ F.obj := liftedResidueConstantDiagonal S p n
  let r := (liftedResidueConstantSheafIso S p n).hom.hom
  let w := (Functor.whiskeringLeft (S.ProEt)ᵒᵖ (T.ProEt)ᵒᵖ Ab.{u+1}).obj (smallProEtRebaseIso σ).op
  let ηT := toSheafify (Scheme.ProEt.topology T) ((Functor.const (T.ProEt)ᵒᵖ).obj M)
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ F.property
  change η ≫ (k ≫ t ≫ l) = η ≫ r
  have hk : η ≫ k = w.map ηT := proEtConstantRebaseIso_unit σ M
  have ht : w.map ηT ≫ t = w.map (liftedResidueConstantDiagonal T p n) :=
    congrArg (fun f => w.map f) (liftedResidueConstantSheafIso_unit T p n)
  calc
    _ = (η ≫ k) ≫ (t ≫ l) := (Category.assoc η k (t ≫ l)).symm
    _ = ((η ≫ k) ≫ t) ≫ l := (Category.assoc (η ≫ k) t l).symm
    _ = (w.map ηT ≫ t) ≫ l := congrArg (fun f => (f ≫ t) ≫ l) hk
    _ = w.map (liftedResidueConstantDiagonal T p n) ≫ l := congrArg (fun f => f ≫ l) ht
    _ = δ := by
      apply NatTrans.ext
      funext W
      apply AddCommGrpCat.hom_ext
      apply DFunLike.ext
      intro a
      rfl
    _ = η ≫ r := (liftedResidueConstantSheafIso_unit S p n).symm

end RC53.EllAdic
