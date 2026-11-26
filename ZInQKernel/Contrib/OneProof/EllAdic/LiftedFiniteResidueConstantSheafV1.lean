import ZInQKernel.Contrib.OneProof.EllAdic.LiftedFiniteResidueLocalInjectivityV1
import ZInQKernel.Contrib.OneProof.EllAdic.LiftedFiniteResidueLocalSurjectivityV2
import ZInQKernel.Contrib.OneProof.EllAdic.PadicProEtSheafLimitV1
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Sites.Equivalence

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite

namespace RC53.EllAdic

universe u

/-- The diagonal is inverted by sheafification on the actual small pro-étale
site, in the coefficient universe used for ell-adic cohomology. -/
theorem liftedResidueConstantDiagonal_W (S : Scheme.{u}) (p n : ℕ) :
    (Scheme.ProEt.topology S).W (liftedResidueConstantDiagonal S p n) := by
  let J := Scheme.ProEt.topology S
  let : EssentiallySmall.{u+1} S.ProEt := inferInstance
  let : J.WEqualsLocallyBijective Ab.{u+1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J
  exact (J.W_iff_isLocallyBijective (liftedResidueConstantDiagonal S p n)).2
    ⟨liftedResidueConstantDiagonal_locallyInjective S p n,
      liftedResidueConstantDiagonal_locallySurjective S p n⟩

/-- The sheafification of the literal constant diagonal identifies the
constant finite residue sheaf with the locally constant residue sheaf. -/
noncomputable def liftedResidueConstantSheafIso (S : Scheme.{u}) (p n : ℕ) :
    (constantSheaf (Scheme.ProEt.topology S) Ab.{u+1}).obj (liftedResidueCoefficient.{u} p n) ≅
      (liftedFiniteResidueProEtSheafTower S p).obj (op n) := by
  let J := Scheme.ProEt.topology S
  let f := liftedResidueConstantDiagonal S p n
  have hIso : IsIso ((presheafToSheaf J Ab.{u+1}).map f) :=
    (J.W_iff f).1 (liftedResidueConstantDiagonal_W S p n)
  let e := @asIso _ _ _ _ ((presheafToSheaf J Ab.{u+1}).map f) hIso
  exact e ≪≫
    ((sheafificationNatIso J Ab.{u+1}).app ((liftedFiniteResidueProEtSheafTower S p).obj (op n))).symm

/-- The same isomorphisms compare the actual reduction maps; this is not
merely a collection of unrelated isomorphisms at individual depths. -/
theorem liftedResidueConstantSheafIso_reduction (S : Scheme.{u}) (p : ℕ)
    {m n : ℕ} (h : m ≤ n) :
    (constantSheaf (Scheme.ProEt.topology S) Ab.{u+1}).map
        (liftedResidueCoefficientTransition.{u} p h) ≫ (liftedResidueConstantSheafIso S p m).hom =
      (liftedResidueConstantSheafIso S p n).hom ≫
        (liftedFiniteResidueProEtSheafTower S p).map (homOfLE h).op := by
  let J := Scheme.ProEt.topology S
  let P := presheafToSheaf J Ab.{u+1}
  let Fm := (liftedFiniteResidueProEtSheafTower S p).obj (op m)
  let Fn := (liftedFiniteResidueProEtSheafTower S p).obj (op n)
  let t : Fn ⟶ Fm := (liftedFiniteResidueProEtSheafTower S p).map (homOfLE h).op
  let i := sheafificationNatIso J Ab.{u+1}
  let u : P.obj Fm.obj ⟶ Fm := i.inv.app Fm
  let v : P.obj Fn.obj ⟶ Fn := i.inv.app Fn
  let d := (Functor.const (S.ProEt)ᵒᵖ).map (liftedResidueCoefficientTransition.{u} p h)
  let δm : _ ⟶ Fm.obj := liftedResidueConstantDiagonal S p m
  let δn : _ ⟶ Fn.obj := liftedResidueConstantDiagonal S p n
  let ρ : Fn.obj ⟶ Fm.obj := t.hom
  change P.map d ≫ P.map δm ≫ u = (P.map δn ≫ v) ≫ t
  have ht : P.map ρ ≫ u = v ≫ t := i.inv.naturality t
  have hd : d ≫ δm = δn ≫ ρ := (liftedResidueConstantDiagonal_reduction S p h).symm
  calc
    P.map d ≫ P.map δm ≫ u = (P.map d ≫ P.map δm) ≫ u :=
      (Category.assoc (P.map d) (P.map δm) u).symm
    _ = P.map (d ≫ δm) ≫ u := congrArg (fun k => k ≫ u) (P.map_comp d δm).symm
    _ = P.map (δn ≫ ρ) ≫ u := congrArg (fun k => P.map k ≫ u) hd
    _ = (P.map δn ≫ P.map ρ) ≫ u := congrArg (fun k => k ≫ u) (P.map_comp δn ρ)
    _ = P.map δn ≫ P.map ρ ≫ u := Category.assoc (P.map δn) (P.map ρ) u
    _ = P.map δn ≫ v ≫ t := congrArg (fun k => P.map δn ≫ k) ht
    _ = (P.map δn ≫ v) ≫ t := (Category.assoc (P.map δn) v t).symm

end RC53.EllAdic
