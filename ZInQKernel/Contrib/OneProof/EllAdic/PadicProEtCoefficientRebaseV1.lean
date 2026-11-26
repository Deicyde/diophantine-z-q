import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.CategoryTheory.Sites.Continuous
import ZInQKernel.Contrib.OneProof.EllAdic.PadicProEtSheafLimitV1
import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleProEtRebaseMateV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite

namespace RC53.EllAdic

universe u

variable {S T : Scheme.{u}} (σ : S ≅ T)

private abbrev proEtToScheme (X : Scheme.{u}) : X.ProEt ⥤ Scheme.{u} :=
  Scheme.ProEt.forget X ⋙ Over.forget X

private theorem smallProEtRebaseIso_op_forget :
    (smallProEtRebaseIso σ).op ⋙ (proEtToScheme T).op = (proEtToScheme S).op := by
  change (((smallProEtRebaseIso σ ⋙ Scheme.ProEt.forget T) ⋙ Over.forget T).op) =
    ((Scheme.ProEt.forget S ⋙ Over.forget S).op)
  exact congrArg Functor.op (smallProEtRebaseIso_forget σ)

private abbrev liftedProEtOfScheme (X : Scheme.{u}) (A : Scheme.{u}ᵒᵖ ⥤ Ab.{u}) :
    (X.ProEt)ᵒᵖ ⥤ Ab.{u+1} :=
  (proEtToScheme X).op ⋙ A ⋙ AddCommGrpCat.uliftFunctor.{u+1,u}

/-- Rebase the restrictions of a single presheaf on schemes. Use identity
components, not the transport maps of an equality of presheaves. -/
private noncomputable def liftedProEtOfScheme_rebase (A : Scheme.{u}ᵒᵖ ⥤ Ab.{u}) :
    (smallProEtRebaseIso σ).op ⋙ liftedProEtOfScheme T A ≅ liftedProEtOfScheme S A :=
  Iso.refl _

/-- `λ_n`: a restricted finite residue sheaf is the literal finite residue
sheaf on the new base, with identity components on sections. -/
noncomputable def liftedFiniteResidueProEtRebaseIso (p n : ℕ) :
    (proEtAbRebasePullback σ).obj ((liftedFiniteResidueProEtSheafTower T p).obj (op n)) ≅
      (liftedFiniteResidueProEtSheafTower S p).obj (op n) :=
  ObjectProperty.isoMk _ (liftedProEtOfScheme_rebase σ (finiteResidueSchemePresheaf.{u} p n))

/-- `λ_I`: the actual lifted integral coefficient sheaf, before applying
cohomology. Its components are identities on continuous sections. -/
noncomputable def continuousResidueProEtRebaseIso (p : ℕ) [Fact p.Prime] :
    (proEtAbRebasePullback σ).obj (continuousResidueProEtSheafCone T p).pt ≅
      (continuousResidueProEtSheafCone S p).pt :=
  ObjectProperty.isoMk _ (liftedProEtOfScheme_rebase σ
    (continuousMapPresheafAb (ℤ_[p]) : Scheme.{u}ᵒᵖ ⥤ Ab.{u}))

@[simp] theorem liftedFiniteResidueProEtRebaseIso_hom_apply (p n : ℕ)
    (W : S.ProEt) (f : ULift.{u+1} (LocallyConstant W.left (ZMod (p ^ n)))) :
    (liftedFiniteResidueProEtRebaseIso σ p n).hom.hom.app (op W) f = f := rfl

@[simp] theorem liftedFiniteResidueProEtRebaseIso_inv_apply (p n : ℕ)
    (W : S.ProEt) (f : ULift.{u+1} (LocallyConstant W.left (ZMod (p ^ n)))) :
    (liftedFiniteResidueProEtRebaseIso σ p n).inv.hom.app (op W) f = f := rfl

@[simp] theorem continuousResidueProEtRebaseIso_hom_apply (p : ℕ) [Fact p.Prime]
    (W : S.ProEt) (f : ULift.{u+1} (C(W.left, ℤ_[p]))) :
    (continuousResidueProEtRebaseIso σ p).hom.hom.app (op W) f = f := rfl

@[simp] theorem continuousResidueProEtRebaseIso_inv_apply (p : ℕ) [Fact p.Prime]
    (W : S.ProEt) (f : ULift.{u+1} (C(W.left, ℤ_[p]))) :
    (continuousResidueProEtRebaseIso σ p).inv.hom.app (op W) f = f := rfl

/-- Naturality for every transition of the actual finite residue tower.
At a section and a point both routes evaluate the same residue projection. -/
theorem liftedFiniteResidueProEtRebaseIso_naturality (p : ℕ) {i j : ℕᵒᵖ} (a : i ⟶ j) :
    (proEtAbRebasePullback σ).map ((liftedFiniteResidueProEtSheafTower T p).map a) ≫
        (liftedFiniteResidueProEtRebaseIso σ p j.unop).hom =
      (liftedFiniteResidueProEtRebaseIso σ p i.unop).hom ≫
        (liftedFiniteResidueProEtSheafTower S p).map a := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply DFunLike.ext
  intro f
  change ULift.{u+1} (LocallyConstant W.unop.left (ZMod (p ^ i.unop))) at f
  apply ULift.ext
  apply LocallyConstant.ext
  intro x
  change padicResidueProjection p (leOfHom a.unop) (f.down x) =
    padicResidueProjection p (leOfHom a.unop) (f.down x)
  rfl

/-- The finite isomorphisms, bundled as an isomorphism of the whole tower. -/
noncomputable def liftedFiniteResidueProEtSheafTowerRebaseIso (p : ℕ) :
    liftedFiniteResidueProEtSheafTower T p ⋙ proEtAbRebasePullback σ ≅
      liftedFiniteResidueProEtSheafTower S p :=
  NatIso.ofComponents (fun i => liftedFiniteResidueProEtRebaseIso σ p i.unop)
    (fun a => liftedFiniteResidueProEtRebaseIso_naturality σ p a)

/-- The transition square, spelled with the actual preorder arrow. -/
theorem liftedFiniteResidueProEtRebaseIso_transition (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    (proEtAbRebasePullback σ).map ((liftedFiniteResidueProEtSheafTower T p).map (homOfLE h).op) ≫
        (liftedFiniteResidueProEtRebaseIso σ p m).hom =
      (liftedFiniteResidueProEtRebaseIso σ p n).hom ≫
        (liftedFiniteResidueProEtSheafTower S p).map (homOfLE h).op :=
  liftedFiniteResidueProEtRebaseIso_naturality σ p (homOfLE h).op

/-- The projection square for the actual cone and its actual legs.
At a section and a point both routes apply `PadicInt.toZModPow n`. -/
theorem continuousResidueProEtRebaseIso_projection (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (proEtAbRebasePullback σ).map ((continuousResidueProEtSheafCone T p).π.app (op n)) ≫
        (liftedFiniteResidueProEtRebaseIso σ p n).hom =
      (continuousResidueProEtRebaseIso σ p).hom ≫
        (continuousResidueProEtSheafCone S p).π.app (op n) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply DFunLike.ext
  intro f
  change ULift.{u+1} (C(W.unop.left, ℤ_[p])) at f
  apply ULift.ext
  apply LocallyConstant.ext
  intro x
  change PadicInt.toZModPow n (f.down x) = PadicInt.toZModPow n (f.down x)
  rfl

end RC53.EllAdic
