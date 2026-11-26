import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleResidueDiagonalV1
import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleAbPullbackV1
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Sites.Equivalence

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite

namespace RC53.EllAdic

universe u

/-- The finite residue sheaf restricted by the actual direct image. -/
noncomputable abbrev smallEtaleResidueSheaf (S : Scheme.{u}) (p n : ℕ) :=
  (smallEtaleAbPushforward S).obj ((liftedFiniteResidueProEtSheafTower S p).obj (op n))

/-- The same residue functions recover the constant sheaf on the small étale
site by the literal constant diagonal. -/
noncomputable def smallEtaleResidueSheafIso (S : Scheme.{u}) (p n : ℕ) :
    (constantSheaf S.smallEtaleTopology Ab.{u+1}).obj (liftedResidueCoefficient.{u} p n) ≅
      smallEtaleResidueSheaf S p n := by
  let J := S.smallEtaleTopology
  let : EssentiallySmall.{u+1} S.Etale := inferInstance
  let : J.WEqualsLocallyBijective Ab.{u+1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J
  let F := smallEtaleResidueSheaf S p n
  let δ : (Functor.const (S.Etale)ᵒᵖ).obj (liftedResidueCoefficient.{u} p n) ⟶ F.obj :=
    smallEtaleResidueDiagonal S p n
  have hW : J.W δ := (J.W_iff_isLocallyBijective δ).2
    ⟨smallEtaleResidueDiagonal_locallyInjective S p n,
      smallEtaleResidueDiagonal_locallySurjective S p n⟩
  have hIso : IsIso ((presheafToSheaf J Ab.{u+1}).map δ) := (J.W_iff δ).1 hW
  let e := @asIso _ _ _ _ ((presheafToSheaf J Ab.{u+1}).map δ) hIso
  exact e ≪≫ ((sheafificationNatIso J Ab.{u+1}).app F).symm

/-- The isomorphism just constructed commutes with literal reduction. -/
theorem smallEtaleResidueSheafIso_reduction (S : Scheme.{u}) (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    (constantSheaf S.smallEtaleTopology Ab.{u+1}).map (liftedResidueCoefficientTransition.{u} p h) ≫
        (smallEtaleResidueSheafIso S p m).hom =
      (smallEtaleResidueSheafIso S p n).hom ≫
        (smallEtaleAbPushforward S).map ((liftedFiniteResidueProEtSheafTower S p).map (homOfLE h).op) := by
  let J := S.smallEtaleTopology
  let P := presheafToSheaf J Ab.{u+1}
  let Fm := smallEtaleResidueSheaf S p m
  let Fn := smallEtaleResidueSheaf S p n
  let t : Fn ⟶ Fm := (smallEtaleAbPushforward S).map
    ((liftedFiniteResidueProEtSheafTower S p).map (homOfLE h).op)
  let u : P.obj Fm.obj ⟶ Fm := (sheafificationNatIso J Ab.{u+1}).inv.app Fm
  let v : P.obj Fn.obj ⟶ Fn := (sheafificationNatIso J Ab.{u+1}).inv.app Fn
  let d := (Functor.const (S.Etale)ᵒᵖ).map (liftedResidueCoefficientTransition.{u} p h)
  let δm : _ ⟶ Fm.obj := smallEtaleResidueDiagonal S p m
  let δn : _ ⟶ Fn.obj := smallEtaleResidueDiagonal S p n
  let ρ : Fn.obj ⟶ Fm.obj := t.hom
  change P.map d ≫ P.map δm ≫ u = (P.map δn ≫ v) ≫ t
  have ht : P.map ρ ≫ u = v ≫ t := (sheafificationNatIso J Ab.{u+1}).inv.naturality t
  have hd : d ≫ δm = δn ≫ ρ := by
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply DFunLike.ext
    intro a
    rfl
  exact (Category.assoc (P.map d) (P.map δm) u).symm.trans
    ((congrArg (fun k => k ≫ u) (P.map_comp d δm).symm).trans
    ((congrArg (fun k => P.map k ≫ u) hd).trans
    ((congrArg (fun k => k ≫ u) (P.map_comp δn ρ)).trans
    ((Category.assoc (P.map δn) (P.map ρ) u).trans
    ((congrArg (fun k => P.map δn ≫ k) ht).trans
      (Category.assoc (P.map δn) v t).symm)))))

end RC53.EllAdic
