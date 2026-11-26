import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleResidueUnitV1
import ZInQKernel.Contrib.OneProof.EllAdic.ExtOneExactAdjunctionV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace RC53.EllAdic

universe u

local instance (S : Scheme.{u}) :
    IsGrothendieckAbelian.{u+1} (Sheaf S.smallEtaleTopology Ab.{u+1}) := by
  let : EssentiallySmall.{u+1} S.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall S.smallEtaleTopology Ab.{u+1}

/-- Literal constant coefficient on the small étale site. -/
noncomputable abbrev etaleConstantResidue (S : Scheme.{u}) (p n : ℕ) :=
  (constantSheaf S.smallEtaleTopology Ab.{u+1}).obj (liftedResidueCoefficient.{u} p n)

/-- Transporting the inverse image of the étale residue tower compares the
same adjacent reduction, using the actual constant-sheaf naturality. -/
theorem smallEtalePulledResidueIso_reduction (S : Scheme.{u}) (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    (smallEtaleAbPullback S).map ((constantSheaf S.smallEtaleTopology Ab.{u+1}).map
        (liftedResidueCoefficientTransition.{u} p h)) ≫ (smallEtalePulledResidueIso S p m).hom =
      (smallEtalePulledResidueIso S p n).hom ≫ (liftedFiniteResidueProEtSheafTower S p).map (homOfLE h).op := by
  let d := liftedResidueCoefficientTransition.{u} p h
  let a := (constantSheaf S.smallEtaleTopology Ab.{u+1}).map d
  let b := (constantSheaf (Scheme.ProEt.topology S) Ab.{u+1}).map d
  let k := (smallEtaleAbPullback S).map a
  let f := (smallEtaleConstantComparison S).hom.app (liftedResidueCoefficient.{u} p n)
  let g := (smallEtaleConstantComparison S).hom.app (liftedResidueCoefficient.{u} p m)
  let i := (liftedResidueConstantSheafIso S p n).hom
  let j := (liftedResidueConstantSheafIso S p m).hom
  let r := (liftedFiniteResidueProEtSheafTower S p).map (homOfLE h).op
  have hc : k ≫ g = f ≫ b := (smallEtaleConstantComparison S).hom.naturality d
  have hr : b ≫ j = i ≫ r := liftedResidueConstantSheafIso_reduction S p h
  change k ≫ (g ≫ j) = (f ≫ i) ≫ r
  exact (Category.assoc k g j).symm.trans ((congrArg (fun t => t ≫ j) hc).trans
    ((Category.assoc f b j).trans ((congrArg (fun t => f ≫ t) hr).trans (Category.assoc f i r).symm)))

private noncomputable abbrev smallEtaleHSource (S : Scheme.{u}) :=
  (constantSheaf S.smallEtaleTopology Ab.{u+1}).obj (AddCommGrpCat.of (ULift.{u+1} ℤ))

private noncomputable abbrev smallProEtHSource (S : Scheme.{u}) :=
  (constantSheaf (Scheme.ProEt.topology S) Ab.{u+1}).obj (AddCommGrpCat.of (ULift.{u+1} ℤ))

private noncomputable abbrev smallEtaleHSourceIso (S : Scheme.{u}) :
    (smallEtaleAbPullback S).obj (smallEtaleHSource S) ≅ smallProEtHSource S :=
  (smallEtaleConstantComparison S).app (AddCommGrpCat.of (ULift.{u+1} ℤ))

/-- The actual finite degree-one pullback followed by the canonical comparison
of each endpoint; the map exists before bijectivity is proved. -/
noncomputable def smallEtaleResidueHOneForward (S : Scheme.{u}) (p n : ℕ) :
    (etaleConstantResidue S p n).H 1 →+ ((liftedFiniteResidueProEtSheafTower S p).obj (op n)).H 1 :=
  let L := smallEtaleAbPullback S
  let X := smallEtaleHSource S
  let Y := etaleConstantResidue S p n
  ((Ext.mk₀ (smallEtalePulledResidueIso S p n).hom).postcomp (smallProEtHSource S) (add_zero 1)).comp
    (((Ext.mk₀ (smallEtaleHSourceIso S).inv).precomp (L.obj Y) (zero_add 1)).comp
      (L.mapExtAddHom X Y 1))

/-- The exact geometric premise left in degree one is that direct image
preserves the epi in the single displayed injective cokernel presentation. -/
theorem smallEtaleResidueHOneForward_bijective_of_specific_epi (S : Scheme.{u}) (p n : ℕ)
    {I Q : Sheaf (Scheme.ProEt.topology S) Ab.{u+1}} [Injective I]
    (i : (smallEtaleAbPullback S).obj (etaleConstantResidue S p n) ⟶ I) [Mono i]
    (q : I ⟶ Q) (w : i ≫ q = 0) (c : IsColimit (CokernelCofork.ofπ q w))
    [Epi ((smallEtaleAbPushforward S).map q)] : Function.Bijective (smallEtaleResidueHOneForward S p n) := by
  let X := smallEtaleHSource S
  let L := smallEtaleAbPullback S
  let Y := etaleConstantResidue S p n
  let V := (liftedFiniteResidueProEtSheafTower S p).obj (op n)
  let Z := smallProEtHSource S
  let a := smallEtaleHSourceIso S
  let b := smallEtalePulledResidueIso S p n
  let : IsIso ((smallEtaleAbAdjunction S).unit.app Y) := smallEtaleResidue_unit_isIso S p n
  have hf := mapExtOne_bijective_of_specific_epi (smallEtaleAbAdjunction S) X Y i q w c
  let s : Ext (L.obj X) (L.obj Y) 1 →+ Ext Z (L.obj Y) 1 := (Ext.mk₀ a.inv).precomp _ (zero_add 1)
  let s' : Ext Z (L.obj Y) 1 →+ Ext (L.obj X) (L.obj Y) 1 := (Ext.mk₀ a.hom).precomp _ (zero_add 1)
  have hs : Function.Bijective s := ⟨(show Function.LeftInverse s' s from by
    intro x
    change (Ext.mk₀ a.hom).comp ((Ext.mk₀ a.inv).comp x (zero_add 1)) (zero_add 1) = x
    rw [Ext.mk₀_comp_mk₀_assoc, a.hom_inv_id, Ext.mk₀_id_comp]).injective,
    (show Function.RightInverse s' s from by
      intro x
      change (Ext.mk₀ a.inv).comp ((Ext.mk₀ a.hom).comp x (zero_add 1)) (zero_add 1) = x
      rw [Ext.mk₀_comp_mk₀_assoc, a.inv_hom_id, Ext.mk₀_id_comp]).surjective⟩
  let t : Ext Z (L.obj Y) 1 →+ Ext Z V 1 := (Ext.mk₀ b.hom).postcomp _ (add_zero 1)
  let t' : Ext Z V 1 →+ Ext Z (L.obj Y) 1 := (Ext.mk₀ b.inv).postcomp _ (add_zero 1)
  have ht : Function.Bijective t := ⟨(show Function.LeftInverse t' t from by
    intro x
    change (x.comp (Ext.mk₀ b.hom) (add_zero 1)).comp (Ext.mk₀ b.inv) (add_zero 1) = x
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, b.hom_inv_id, Ext.comp_mk₀_id]).injective,
    (show Function.RightInverse t' t from by
      intro x
      change (x.comp (Ext.mk₀ b.inv) (add_zero 1)).comp (Ext.mk₀ b.hom) (add_zero 1) = x
      rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, b.inv_hom_id, Ext.comp_mk₀_id]).surjective⟩
  exact ht.comp (hs.comp hf)

end RC53.EllAdic
