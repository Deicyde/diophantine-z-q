import ZInQKernel.Contrib.OneProof.SZThm33.TateIdentityComponent
import ZInQKernel.Contrib.OneProof.PersistsDVR

/-! The open-immersion criterion transports semistability back through the
canonical comparison and through algebraic residue extension. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace Topology
open ReductSplit ReductGlue ZInQ.HeightSplit ZInQ.SemiAbDescend

set_option linter.style.haveILetI false

namespace SZRaynaud

set_option backward.isDefEq.respectTransparency false in
/-- An open subgroup of a group with semiabelian identity component has
the same semiabelian identity component. -/
theorem hasSemiAbelianIdentityComponent_of_openSubgroup
    {k : Type} [Field k] [IsAlgClosed k]
    {X Y : Over (Spec (.of k))} [GrpObj X] [GrpObj Y] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsOpenImmersion f.left] [IsMonHom f]
    (hY : HasSemiAbelianIdentityComponent Y) :
    HasSemiAbelianIdentityComponent X := by
  obtain ⟨U, gU, i, hi, hiM, hu, rest⟩ := hY
  letI : GrpObj U := gU
  haveI : IsOpenImmersion i.left := hi
  haveI : IsMonHom i := hiM
  haveI : ConnectedSpace U.left := hu
  let pt := 𝟙_ (Over (Spec (.of k)))
  have hη : (1 : pt ⟶ Y).left (IsLocalRing.closedPoint k) ∈ Set.range f.left :=
    ⟨(1 : pt ⟶ X).left (IsLocalRing.closedPoint k),
      congrArg (fun p : pt ⟶ Y => p.left (IsLocalRing.closedPoint k))
        (map_one (mapGroupPoint (P := pt) f))⟩
  have hre : Set.range i.left ⊆ Set.range f.left := by
    rw [range_openConnectedSubgroup_eq_connectedComponent i]
    exact IsClopen.connectedComponent_subset
      ⟨isClosed_range_openSubgroup f, f.left.isOpenEmbedding.isOpen_range⟩ hη
  let v : U ⟶ X := Over.homMk (IsOpenImmersion.lift f.left i.left hre) (by
    rw [← Over.w f, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w])
  have hv : v ≫ f = i := Over.OverMorphism.ext (IsOpenImmersion.lift_fac ..)
  haveI : IsOpenImmersion (v.left ≫ f.left) := by rw [← Over.comp_left, hv]; exact hi
  haveI : Mono f := Over.mono_of_mono_left f
  haveI : IsMonHom (v ≫ f) := hv ▸ hiM
  exact ⟨U, gU, v, IsOpenImmersion.of_comp v.left f.left,
    AVGlue.isMonHom_of_comp_mono v f, hu, rest⟩

set_option backward.isDefEq.respectTransparency false in
/-- Any open immersion comparing the two models descends geometric
semistability from the finite extension to the original model. -/
theorem isSemistable_of_openComparison
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {O : ValuationSubring K} {P : ValuationSubring L}
    (hP : P.comap (algebraMap K L) = O)
    (A : PkgI3.AbVar K) (M : GroupModelO A O) (N : GroupModelO (A.baseChange L) P)
    (f : (bcDVR hP M).G ⟶ N.G) [IsOpenImmersion f.left] [IsMonHom f]
    (hN : N.IsSemistable) : M.IsSemistable := by
  let d := Spec.map (CommRingCat.ofHom (algebraMap P (ResBarO P)))
  let b : geomSpecialFibre (bcDVR hP M) ⟶ geomSpecialFibre N := (Over.pullback d).map f
  haveI : IsOpenImmersion b.left := ZInQ.H5Glue.isOpenImmersion_pullback_map d f
  haveI : IsMonHom b := Functor.map.instIsMonHom (F := Over.pullback d) _ _ f
  haveI : LocallyOfFiniteType (geomSpecialFibre N).hom :=
    show LocallyOfFiniteType (pullback.snd N.G.hom d) by infer_instance
  exact (isSemistable_bcDVR_iff hP (GapPersists.isAlgebraic_resMap hP) M).mpr
    (hasSemiAbelianIdentityComponent_of_openSubgroup b hN)

#print axioms hasSemiAbelianIdentityComponent_of_openSubgroup
#print axioms isSemistable_of_openComparison

end SZRaynaud
