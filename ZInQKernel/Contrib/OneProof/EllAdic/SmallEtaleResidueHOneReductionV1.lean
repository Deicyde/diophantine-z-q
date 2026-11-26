import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleResidueHOneForwardV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Opposite

namespace RC53.EllAdic

universe u

local instance (S : Scheme.{u}) :
    IsGrothendieckAbelian.{u+1} (Sheaf S.smallEtaleTopology Ab.{u+1}) := by
  let : EssentiallySmall.{u+1} S.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall S.smallEtaleTopology Ab.{u+1}

/-- The actual cohomology comparison commutes with the same literal
reductions verified on the two coefficient towers. This does not require
bijectivity or any preservation of epis by direct image. -/
theorem smallEtaleResidueHOneForward_reduction (S : Scheme.{u}) (p : ℕ) {m n : ℕ} (h : m ≤ n)
    (x : (etaleConstantResidue S p n).H 1) :
    Sheaf.H.map ((liftedFiniteResidueProEtSheafTower S p).map (homOfLE h).op) 1
        (smallEtaleResidueHOneForward S p n x) =
      smallEtaleResidueHOneForward S p m
        (Sheaf.H.map ((constantSheaf S.smallEtaleTopology Ab.{u+1}).map
          (liftedResidueCoefficientTransition.{u} p h)) 1 x) := by
  let L := smallEtaleAbPullback S
  let d := (constantSheaf S.smallEtaleTopology Ab.{u+1}).map (liftedResidueCoefficientTransition.{u} p h)
  let r := (liftedFiniteResidueProEtSheafTower S p).map (homOfLE h).op
  let a := (smallEtaleConstantComparison S).inv.app (AddCommGrpCat.of (ULift.{u+1} ℤ))
  let b := (smallEtalePulledResidueIso S p n).hom
  let c := (smallEtalePulledResidueIso S p m).hom
  let α := Ext.mk₀ a
  let X := (constantSheaf S.smallEtaleTopology Ab.{u+1}).obj (AddCommGrpCat.of (ULift.{u+1} ℤ))
  let y := L.mapExtAddHom X (etaleConstantResidue S p n) 1 x
  let z := L.mapExtAddHom X (etaleConstantResidue S p m) 1 (Sheaf.H.map d 1 x)
  have hz : z = y.comp (Ext.mk₀ (L.map d)) (add_zero 1) := by
    change (x.comp (Ext.mk₀ d) (add_zero 1)).mapExactFunctor L = _
    exact (Ext.mapExactFunctor_comp L x (Ext.mk₀ d) (add_zero 1)).trans
      (congrArg (fun t => y.comp t (add_zero 1)) (Ext.mapExactFunctor_mk₀ L d))
  have hb : L.map d ≫ c = b ≫ r := smallEtalePulledResidueIso_reduction S p h
  change ((α.comp y (zero_add 1)).comp (Ext.mk₀ b) (add_zero 1)).comp (Ext.mk₀ r) (add_zero 1) =
    (α.comp z (zero_add 1)).comp (Ext.mk₀ c) (add_zero 1)
  have e₁ : ((α.comp y (zero_add 1)).comp (Ext.mk₀ b) (add_zero 1)).comp (Ext.mk₀ r) (add_zero 1) =
      (α.comp y (zero_add 1)).comp (Ext.mk₀ (b ≫ r)) (add_zero 1) := by
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  have e₂ : (α.comp z (zero_add 1)).comp (Ext.mk₀ c) (add_zero 1) =
      (α.comp y (zero_add 1)).comp (Ext.mk₀ (L.map d ≫ c)) (add_zero 1) := by
    rw [hz, ← Ext.comp_assoc_of_third_deg_zero α y (Ext.mk₀ (L.map d)) (zero_add 1)]
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  exact e₁.trans ((congrArg (fun t => (α.comp y (zero_add 1)).comp (Ext.mk₀ t) (add_zero 1)) hb.symm).trans e₂.symm)

end RC53.EllAdic
