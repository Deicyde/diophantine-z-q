import ZInQKernel.HDecomp.Objects
import ZInQKernel.OneProof.H.TailP
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Group.QuasiProjective

/-!
Private graph-route scouting prototypes. No graph algebraization is asserted.
The projective embedding below is of the actual abelian variety, not of a Chow cover.
The point-bijective projection criterion below keeps its reduced self-pullback input explicit.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bGraphScout

/-- The actual proper smooth geometrically integral group admits a projective closed embedding. -/
theorem abVar_exists_projective_closed_embedding (A : PkgI3.AbVar ℂ) :
    ∃ (idx : Type) (_ : Finite idx) (e : A.X.left ⟶ ℙ(idx; Spec (.of ℂ))),
      IsClosedImmersion e ∧ e ≫ ℙ(idx; Spec (.of ℂ)) ↘ Spec (.of ℂ) = A.X.hom := by
  obtain ⟨idx, hidx, e, he, hbase⟩ :=
    AlgebraicGeometry.GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral A.X
  letI := hidx
  letI := he
  haveI : IsProper (e ≫ ℙ(idx; Spec (.of ℂ)) ↘ Spec (.of ℂ)) := by
    rw [hbase]
    infer_instance
  haveI : IsProper e := IsProper.of_comp e (ℙ(idx; Spec (.of ℂ)) ↘ Spec (.of ℂ))
  exact ⟨idx, hidx, e, IsClosedImmersion.of_isPreimmersion e e.isClosedMap.isClosed_range, hbase⟩

/-- Projectivity is available for the actual graph ambient group A×B, not just a cover. -/
theorem prodAbVar_exists_projective_closed_embedding (A B : PkgI3.AbVar ℂ) :
    ∃ (idx : Type) (_ : Finite idx) (e : (A.X ⊗ B.X).left ⟶ ℙ(idx; Spec (.of ℂ))),
      IsClosedImmersion e ∧ e ≫ ℙ(idx; Spec (.of ℂ)) ↘ Spec (.of ℂ) = (A.X ⊗ B.X).hom :=
  abVar_exists_projective_closed_embedding (AVGlue.prodAbVar A B)

/-- A proper morphism surjective on complex points is surjective on all scheme points.
Closed-point density is used only AFTER an algebraic morphism exists. -/
theorem surjective_of_proper_of_complexPoints
    {X Y : Over (Spec (.of ℂ))} (p : X ⟶ Y) [IsProper p.left]
    [LocallyOfFiniteType Y.hom]
    (hp : Function.Surjective (fun t : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ X => t ≫ p)) :
    Surjective p.left := by
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have hc : IsClosed (Set.range p.left) := p.left.isClosedMap.isClosed_range
  have hpts : closedPoints Y.left ⊆ Set.range p.left := by
    intro y hy
    let t : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ Y :=
      Over.homMk (pointOfClosedPoint Y.hom y hy) (pointOfClosedPoint_comp Y.hom y hy)
    obtain ⟨s, hs⟩ := hp t
    refine ⟨s.left (IsLocalRing.closedPoint ℂ), ?_⟩
    have he := congrArg (fun q : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ Y =>
      q.left (IsLocalRing.closedPoint ℂ)) hs
    change p.left (s.left (IsLocalRing.closedPoint ℂ)) =
      pointOfClosedPoint Y.hom y hy (IsLocalRing.closedPoint ℂ) at he
    exact he.trans (pointOfClosedPoint_apply Y.hom y hy (IsLocalRing.closedPoint ℂ))
  refine ⟨fun y => ?_⟩
  have : closure (closedPoints Y.left) ⊆ Set.range p.left :=
    hc.closure_subset_iff.mpr hpts
  rw [closure_closedPoints] at this
  exact this (Set.mem_univ y)

/-- Reduced self-pullback plus injectivity on actual complex points gives a categorical mono.
It is not valid to drop the reduced self-pullback condition for arbitrary finite morphisms. -/
theorem mono_of_reduced_selfPullback_of_complexPoints
    {X Y : Over (Spec (.of ℂ))} (p : X ⟶ Y)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType p.left] [IsSeparated X.hom]
    [IsReduced (pullback p.left p.left)]
    (hp : Function.Injective (fun t : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ X => t ≫ p)) :
    Mono p.left := by
  have hbase : pullback.fst p.left p.left ≫ X.hom =
      pullback.snd p.left p.left ≫ X.hom := by
    rw [← p.w, ← Category.assoc, pullback.condition, Category.assoc]
  have hproj : pullback.fst p.left p.left = pullback.snd p.left p.left := by
    apply ext_of_apply_eq X.hom Set.univ isOpen_univ.isLocallyClosed dense_univ
    · intro z _ hz
      let D : Over (Spec (.of ℂ)) :=
        Over.mk (pullback.fst p.left p.left ≫ X.hom)
      haveI : LocallyOfFiniteType D.hom := by
        dsimp only [D, Over.mk_hom]
        infer_instance
      let t : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ D :=
        Over.homMk (pointOfClosedPoint D.hom z hz) (pointOfClosedPoint_comp D.hom z hz)
      let f : D ⟶ X := Over.homMk (pullback.fst p.left p.left) rfl
      let g : D ⟶ X := Over.homMk (pullback.snd p.left p.left) hbase.symm
      have hfg : (t ≫ f) ≫ p = (t ≫ g) ≫ p := by
        apply Over.OverMorphism.ext
        simp only [Over.comp_left, f, g, Over.homMk_left, Category.assoc]
        rw [pullback.condition]
      have he := congrArg (fun q : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ X =>
        q.left (IsLocalRing.closedPoint ℂ)) (hp hfg)
      change pullback.fst p.left p.left (t.left (IsLocalRing.closedPoint ℂ)) =
        pullback.snd p.left p.left (t.left (IsLocalRing.closedPoint ℂ)) at he
      have ht : t.left (IsLocalRing.closedPoint ℂ) = z :=
        pointOfClosedPoint_apply D.hom z hz (IsLocalRing.closedPoint ℂ)
      simpa only [ht] using he
    · exact hbase
  refine ⟨?_⟩
  intro Z f g hfg
  have he := congrArg (fun q => pullback.lift f g hfg ≫ q) hproj
  simpa only [pullback.lift_fst, pullback.lift_snd] using he

/-- The genuine graph projection is an isomorphism once an algebraic proper morphism,
a reduced self-pullback, and the point bijection have actually been supplied. -/
theorem isIso_of_proper_of_reduced_selfPullback_of_complexPoints
    {X Y : Over (Spec (.of ℂ))} (p : X ⟶ Y) [IsProper p.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [IsSeparated X.hom]
    [IsReduced Y.left] [IsReduced (pullback p.left p.left)]
    (hp : Function.Bijective (fun t : Over.mk (𝟙 (Spec (.of ℂ))) ⟶ X => t ≫ p)) :
    IsIso p := by
  haveI : Mono p.left := mono_of_reduced_selfPullback_of_complexPoints p hp.1
  haveI : Surjective p.left := surjective_of_proper_of_complexPoints p hp.2
  haveI : IsClosedImmersion p.left :=
    (IsClosedImmersion.iff_isProper_and_mono p.left).mpr ⟨inferInstance, inferInstance⟩
  haveI : IsIso p.left := isIso_of_isClosedImmersion_of_surjective p.left
  haveI : IsIso ((Over.forget _).map p) := inferInstanceAs (IsIso p.left)
  exact isIso_of_reflects_iso p (Over.forget _)

end ZInQ.Contrib.CloudB3W17bGraphScout
