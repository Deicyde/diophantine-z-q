import ZInQKernel.Contrib.CloudR2Poincare.L3.RegularStalkOfFreeDifferentials
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.AlgebraicGeometry.GroupScheme.Differentials
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
import Mathlib.AlgebraicGeometry.Group.Smooth
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Cartier's theorem, with only its needed proof closure

The group-differential freeness supplier is the port of Stacks 047I. The only
commutative-algebra Cartier input is the proved 00TX direction free differentials
⇒ regular local ring, assembled in `RegularStalkOfFreeDifferentials`. Regular
local rings are domains by the published Tau Ceti supplier, hence every field
base change of the group scheme is reduced. Mathlib's `smooth_of_grpObj` finishes.
No desired Cartier, kernel or Poincaré fact is assumed.
-/

open CategoryTheory AlgebraicGeometry Limits

namespace ZInQ.Contrib.CloudR2Poincare.L3
#cloudR2LocalInstances

open StacksPort.AlgebraicGeometry.Scheme.Hom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

universe u

/-- A sheaf isomorphic to a free sheaf is locally free; the canonical global free basis
    transports along the inverse isomorphism. -/
theorem locallyFree_relativeDifferentials_of_free_iso {X S : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} (e : _root_.ZInQ.Contrib.CloudR2Poincare.L3.StacksPort.AlgebraicGeometry.Scheme.Hom.relativeDifferentials f ≅
      SheafOfModules.free (R := X.ringCatSheaf) I) :
    _root_.SheafOfModules.IsLocallyFree.{u, u, u} (_root_.ZInQ.Contrib.CloudR2Poincare.L3.StacksPort.AlgebraicGeometry.Scheme.Hom.relativeDifferentials f) := by
  exact (StacksPort.Stacks.FiniteLocallyFree.localGeneratorsDataOfIsIso e.inv
    (SheafOfModules.free.generatingSections (R := X.ringCatSheaf) I).localGeneratorsData).isLocallyFree

/-- The locally finite-type case of Cartier reducedness, proved from free group differentials. -/
theorem isReduced_groupScheme_charZero (k : Type u) [Field k] [CharZero k]
    (G : Scheme.{u}) (f : G ⟶ Spec (.of k))
    [GrpObj (Over.mk f)] [LocallyOfFiniteType f] : IsReduced G := by
  obtain ⟨I, ⟨e⟩⟩ :=
    StacksPort.AlgebraicGeometry.GroupSchemeDifferentials.exists_free_iso_relativeDifferentials_of_field
      k G f
  exact isReduced_of_isLocallyFree_relativeDifferentials_charZero f
    (locallyFree_relativeDifferentials_of_free_iso f e)

/-- Field extensions retain characteristic zero, so the same proved reducedness theorem
    applies to every field base change, giving geometric reducedness. -/
theorem geometricallyReduced_groupScheme_charZero (k : Type u) [Field k] [CharZero k]
    (G : Scheme.{u}) (f : G ⟶ Spec (.of k))
    [GrpObj (Over.mk f)] [LocallyOfFiniteType f] : GeometricallyReduced f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y => ?_⟩
  let a : CommRingCat.of k ⟶ CommRingCat.of K := Spec.preimage y
  haveI : CharZero K := charZero_of_injective_ringHom a.hom.injective
  haveI : GrpObj (Over.mk (pullback.snd f y)) := Over.grpObjMkPullbackSnd
  exact isReduced_groupScheme_charZero K (pullback f y) (pullback.snd f y)

/-- **Cartier (Stacks 047N):** a locally finite-type group scheme over a characteristic-zero
    field is smooth. The geometric reducedness input is proved above. -/
theorem smooth_groupScheme_charZero (k : Type u) [Field k] [CharZero k]
    (G : Scheme.{u}) (f : G ⟶ Spec (.of k))
    [GrpObj (Over.mk f)] [LocallyOfFiniteType f] : Smooth f := by
  haveI : GeometricallyReduced f := geometricallyReduced_groupScheme_charZero k G f
  exact AlgebraicGeometry.smooth_of_grpObj f

/-- Cartier in precisely the `Over (Spec k)` group-object form used by `PkgI3.AbVar`. -/
theorem cartierSmooth_proof (k : Type u) [Field k] [CharZero k]
    (G : Over (Spec (.of k))) [GrpObj G] (h : LocallyOfFiniteType G.hom) : Smooth G.hom := by
  have hG : G = Over.mk G.hom := by cases G; rfl
  letI : GrpObj (Over.mk G.hom) := hG ▸ (inferInstance : GrpObj G)
  haveI : LocallyOfFiniteType G.hom := h
  exact smooth_groupScheme_charZero k G.left G.hom

end ZInQ.Contrib.CloudR2Poincare.L3
