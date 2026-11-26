import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleAbPullbackV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace RC53.EllAdic

universe u

private abbrev etaleIdentity (S : Scheme.{u}) : S.Etale := Scheme.Etale.mk (𝟙 S)

private def etaleIdentity_isTerminal (S : Scheme.{u}) : IsTerminal (etaleIdentity S) := by
  letI : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  exact MorphismProperty.Over.mkIdTerminal (@Etale) S

private def proEtImageIdentity_isTerminal (S : Scheme.{u}) :
    IsTerminal ((smallEtaleToProEt S).obj (etaleIdentity S)) := by
  letI : MorphismProperty.ContainsIdentities (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative (@WeaklyEtale : MorphismProperty Scheme.{u})).toContainsIdentities
  exact MorphismProperty.Over.mkIdTerminal (@WeaklyEtale) S

private theorem constPshHomAt {C D : Type*} [Category* C] [Category* D]
    {T : C} (hT : IsTerminal T) (M : D) (P : Cᵒᵖ ⥤ D)
    (f : (Functor.const Cᵒᵖ).obj M ⟶ P) :
    (constantPresheafAdj D hT).homEquiv M P f = f.app (op T) := by
  rw [Adjunction.homEquiv_unit]
  change 𝟙 M ≫ f.app (op T) = f.app (op T)
  exact Category.id_comp _

private theorem constShHomAt {C D : Type*} [Category* C] [Category* D]
    (J : GrothendieckTopology C) [HasWeakSheafify J D] {T : C} (hT : IsTerminal T)
    (M : D) (F : Sheaf J D) (f : (constantSheaf J D).obj M ⟶ F) :
    (constantSheafAdj J D hT).homEquiv M F f =
      (toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫ f.hom).app (op T) := by
  let a := constantPresheafAdj D hT
  let b := sheafificationAdjunction J D
  let P := (Functor.const Cᵒᵖ).obj M
  have hb : b.homEquiv P F f = toSheafify J P ≫ f.hom := rfl
  have hc : (a.comp b).homEquiv M F f = a.homEquiv M F.obj (b.homEquiv P F f) :=
    congrArg (fun k => k M F f) (Adjunction.comp_homEquiv a b)
  exact hc.trans ((constPshHomAt hT M F.obj _).trans
    (congrArg (fun k : P ⟶ F.obj => k.app (op T)) hb))

private theorem constShUnitAt {C D : Type*} [Category* C] [Category* D]
    (J : GrothendieckTopology C) [HasWeakSheafify J D] {T : C} (hT : IsTerminal T) (M : D) :
    (constantSheafAdj J D hT).unit.app M =
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T) := by
  rw [constantSheafAdj, Adjunction.comp_unit_app]
  change 𝟙 M ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T) = _
  exact Category.id_comp _

/-- The canonical comparison for constant sheaves under the actual inverse
image. Both adjunctions use evaluation at the same identity scheme. -/
noncomputable def smallEtaleConstantComparison (S : Scheme.{u}) :
    constantSheaf S.smallEtaleTopology Ab.{u+1} ⋙ smallEtaleAbPullback S ≅
      constantSheaf (Scheme.ProEt.topology S) Ab.{u+1} :=
  Adjunction.leftAdjointUniq
    ((constantSheafAdj S.smallEtaleTopology Ab.{u+1} (etaleIdentity_isTerminal S)).comp
      (smallEtaleAbAdjunction S))
    (constantSheafAdj (Scheme.ProEt.topology S) Ab.{u+1} (proEtImageIdentity_isTerminal S))

/-- The direct image on presheaf sections restricts the literal pro-étale
constant presheaf unit. -/
noncomputable def smallEtaleRestrictedConstantUnit (S : Scheme.{u}) (M : Ab.{u+1}) :
    (Functor.const (S.Etale)ᵒᵖ).obj M ⟶
      ((smallEtaleAbPushforward S).obj
        ((constantSheaf (Scheme.ProEt.topology S) Ab.{u+1}).obj M)).obj :=
  Functor.whiskerLeft (smallEtaleToProEt S).op
    (toSheafify (Scheme.ProEt.topology S) ((Functor.const (S.ProEt)ᵒᵖ).obj M))

/-- The canonical constant comparison transposes to sheafification of the
same restricted constant map, rather than a freely chosen object iso. -/
theorem smallEtaleConstantComparison_transpose (S : Scheme.{u}) (M : Ab.{u+1}) :
    ((smallEtaleAbAdjunction S).homEquiv ((constantSheaf S.smallEtaleTopology Ab.{u+1}).obj M)
      ((constantSheaf (Scheme.ProEt.topology S) Ab.{u+1}).obj M)
      ((smallEtaleConstantComparison S).hom.app M)).hom =
      sheafifyLift S.smallEtaleTopology (smallEtaleRestrictedConstantUnit S M)
        ((smallEtaleAbPushforward S).obj
          ((constantSheaf (Scheme.ProEt.topology S) Ab.{u+1}).obj M)).property := by
  apply sheafifyLift_unique
  apply ((constantPresheafAdj Ab.{u+1} (etaleIdentity_isTerminal S)).homEquiv M
    ((smallEtaleAbPushforward S).obj
      ((constantSheaf (Scheme.ProEt.topology S) Ab.{u+1}).obj M)).obj).injective
  simp only [constPshHomAt]
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((constantSheafAdj S.smallEtaleTopology Ab.{u+1} (etaleIdentity_isTerminal S)).comp
      (smallEtaleAbAdjunction S))
    (constantSheafAdj (Scheme.ProEt.topology S) Ab.{u+1} (proEtImageIdentity_isTerminal S)) M
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply, constShHomAt, constShUnitAt] at h
  exact h

end RC53.EllAdic
