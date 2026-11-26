import ZInQKernel.Contrib.OneProof.EllAdic.PadicCoefficientAdditiveV1
import ZInQKernel.Contrib.OneProof.EllAdic.FiniteResidueSchemeTowerV2
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace RC53.EllAdic

universe u

private noncomputable def continuousResidueReduction (p : ℕ) [Fact p.Prime] (n : ℕ)
    (U : Type*) [TopologicalSpace U] : C(U, ℤ_[p]) →+ LocallyConstant U (ZMod (p ^ n)) where
  toFun f := ⟨fun x => PadicInt.toZModPow n (f x),
    (continuous_iff_locallyConstant_padicReductions f).1 f.continuous n⟩
  map_zero' := by
    apply LocallyConstant.ext
    intro x
    change PadicInt.toZModPow n (0 : ℤ_[p]) = 0
    exact map_zero _
  map_add' f g := by
    apply LocallyConstant.ext
    intro x
    change PadicInt.toZModPow n (f x + g x) =
      PadicInt.toZModPow n (f x) + PadicInt.toZModPow n (g x)
    exact map_add _ _ _

private noncomputable def continuousResidueSchemeReduction (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (continuousMapPresheafAb (ℤ_[p]) : Scheme.{u}ᵒᵖ ⥤ Ab.{u}) ⟶ finiteResidueSchemePresheaf p n where
  app U := AddCommGrpCat.ofHom (continuousResidueReduction p n U.unop)
  naturality _ _ _ := by
    apply AddCommGrpCat.hom_ext
    apply DFunLike.ext
    intro f
    apply LocallyConstant.ext
    intro x
    rfl

/-- The cone whose vertex is the actual continuous-map presheaf, and whose
projections are the literal reductions on the p-adic integers. -/
noncomputable def continuousResidueSchemeCone (p : ℕ) [Fact p.Prime] :
    Cone (finiteResidueSchemeTower.{u} p) where
  pt := continuousMapPresheafAb (ℤ_[p])
  π := {
    app n := continuousResidueSchemeReduction p n.unop
    naturality m n f := by
      apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      apply DFunLike.ext
      intro r
      change C(U.unop, ℤ_[p]) at r
      apply LocallyConstant.ext
      intro x
      change PadicInt.toZModPow n.unop (r x) =
        padicResidueProjection p (leOfHom f.unop) (PadicInt.toZModPow m.unop (r x))
      exact (PadicInt.cast_toZModPow n.unop m.unop (leOfHom f.unop) (r x)).symm }

private abbrev residueSchemeEvaluation (U : Scheme.{u}ᵒᵖ) : (Scheme.{u}ᵒᵖ ⥤ Ab.{u}) ⥤ Ab.{u} :=
  (evaluation (Scheme.{u}ᵒᵖ) Ab.{u}).obj U

private abbrev finiteResidueTowerAt (p : ℕ) (U : Scheme.{u}ᵒᵖ) : ℕᵒᵖ ⥤ Ab.{u} :=
  finiteResidueSchemeTower p ⋙ residueSchemeEvaluation U

private def pointwiseConeCompatibleResidues (p : ℕ) (U : Scheme.{u}ᵒᵖ)
    (s : Cone (finiteResidueTowerAt p U)) : s.pt →+ ↥(compatibleResiduesAddSubgroup p U.unop) where
  toFun a := ⟨fun n x => (show LocallyConstant U.unop (ZMod (p ^ n)) from s.π.app (op n) a) x,
    fun n => (show LocallyConstant U.unop (ZMod (p ^ n)) from s.π.app (op n) a).isLocallyConstant,
    fun n x => by
      let e : op (n + 1) ⟶ op n := (homOfLE (Nat.le_succ n)).op
      exact congrArg (fun g : s.pt ⟶ (finiteResidueTowerAt p U).obj (op n) =>
        (show LocallyConstant U.unop (ZMod (p ^ n)) from g a) x) (s.w e)⟩
  map_zero' := by
    apply Subtype.ext
    funext n x
    exact congrArg (fun f : LocallyConstant U.unop (ZMod (p ^ n)) => f x)
      (map_zero (s.π.app (op n)).hom)
  map_add' a b := by
    apply Subtype.ext
    funext n x
    exact congrArg (fun f : LocallyConstant U.unop (ZMod (p ^ n)) => f x)
      (map_add (s.π.app (op n)).hom a b)

private noncomputable def pointwiseConeLift (p : ℕ) [Fact p.Prime]
    (U : Scheme.{u}ᵒᵖ) (s : Cone (finiteResidueTowerAt p U)) :
    s.pt ⟶ ((residueSchemeEvaluation U).mapCone (continuousResidueSchemeCone p)).pt :=
  AddCommGrpCat.ofHom
    (continuousMapAddEquivCompatibleResidues.symm.toAddMonoidHom.comp
      (pointwiseConeCompatibleResidues p U s))

private lemma pointwiseConeLift_reduce (p : ℕ) [Fact p.Prime] (U : Scheme.{u}ᵒᵖ)
    (s : Cone (finiteResidueTowerAt p U)) (a : s.pt) (n : ℕ) (x : U.unop) :
    PadicInt.toZModPow n ((show C(U.unop, ℤ_[p]) from pointwiseConeLift p U s a) x) =
      (show LocallyConstant U.unop (ZMod (p ^ n)) from s.π.app (op n) a) x :=
  congrArg (fun r : ↥(compatibleResiduesAddSubgroup p U.unop) => r.1 n x)
    (continuousMapAddEquivCompatibleResidues.apply_symm_apply (pointwiseConeCompatibleResidues p U s a))

private noncomputable def continuousResidueSchemeConeAtIsLimit (p : ℕ) [Fact p.Prime]
    (U : Scheme.{u}ᵒᵖ) : IsLimit ((residueSchemeEvaluation U).mapCone (continuousResidueSchemeCone p)) where
  lift s := pointwiseConeLift p U s
  fac s j := by
    apply AddCommGrpCat.hom_ext
    apply DFunLike.ext
    intro a
    apply LocallyConstant.ext
    intro x
    exact pointwiseConeLift_reduce p U s a j.unop x
  uniq s f hf := by
    apply AddCommGrpCat.hom_ext
    apply DFunLike.ext
    intro a
    apply ContinuousMap.ext
    intro x
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    exact (congrArg (fun g : s.pt ⟶ (finiteResidueTowerAt p U).obj (op n) =>
      (show LocallyConstant U.unop (ZMod (p ^ n)) from g a) x)
      (hf (op n))).trans (pointwiseConeLift_reduce p U s a n x).symm

/-- The continuous coefficients exhibit the inverse limit of the finite
residue presheaves. The universal morphism is determined by the same residue
maps after evaluation on each scheme. -/
noncomputable def continuousResidueSchemeConeIsLimit (p : ℕ) [Fact p.Prime] :
    IsLimit (continuousResidueSchemeCone.{u} p) :=
  evaluationJointlyReflectsLimits _ (continuousResidueSchemeConeAtIsLimit p)

end RC53.EllAdic
