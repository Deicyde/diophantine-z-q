/-
Cartier smoothness, H-98. The proof follows Stacks 047N/047I/04QN and
00TX: invariant differentials are free; locally free differentials imply
smoothness in characteristic zero. Selected proof sources and licenses are
recorded in ZInQKernel/Contrib/CloudB3W16Cartier/NOTICE.md.
-/
import ZInQKernel.Contrib.OneProof.H.TailP
import ZInQKernel.Contrib.CloudB3W16Cartier.GroupDifferentials
import ZInQKernel.Contrib.CloudB3W16Cartier.SmoothCriterion
import ZInQKernel.Contrib.CloudB3W16Cartier.Vendor.StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree

namespace ZInQ.Contrib.OneProof.CartierSmooth

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v₁ u₁

/-- A free module sheaf is locally free, also after transport by an isomorphism.
Adapted from Stacks `GroupScheme/OverField/SmoothCharacteristicZero.lean`,
lines 92–100, with the existing proof-level local-generators transport. -/
private theorem isLocallyFree_of_iso_free {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R} {I : Type u} (e : M ≅ SheafOfModules.free (R := R) I) :
    M.IsLocallyFree :=
  (ZInQ.Contrib.CloudB3W16Cartier.Vendor.Stacks.FiniteLocallyFree.localGeneratorsDataOfIsIso e.inv
    (SheafOfModules.free.generatingSections (R := R) I).localGeneratorsData).isLocallyFree

/-- Cartier's theorem with exactly the frozen H-98 hypotheses and conclusion. -/
theorem cartierSmooth_proof : AVGlue.CartierSmooth := by
  intro k _ _ G _ hft
  haveI : LocallyOfFiniteType G.hom := hft
  haveI : GrpObj (Over.mk G.hom) := by
    change GrpObj G
    infer_instance
  obtain ⟨I, ⟨e⟩⟩ :=
    ZInQ.Contrib.CloudB3W16Cartier.Vendor.AlgebraicGeometry.GroupSchemeDifferentials.exists_free_iso_relativeDifferentials_of_field
      k G.left G.hom
  exact ZInQ.Contrib.CloudB3W16Cartier.Vendor.AlgebraicGeometry.smooth_of_isLocallyFree_relativeDifferentials_of_charZero
    G.hom (isLocallyFree_of_iso_free.{0, 0, 0} e)

end ZInQ.Contrib.OneProof.CartierSmooth
