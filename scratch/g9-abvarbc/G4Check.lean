import ZInQKernel.Contrib.AbVarBC.Consumers

/-! Check (task g9-abvarbc): g4-weilres's `bcAlong` (copied verbatim from
`origin/wip/g4-weilres:scratch/g4-weilres/G4.lean` L955-962, renamed `bcAlong'`) has the dimension of
`A`, through `ZInQ.Contrib.AbVarBC.dim_overPullback`. -/

open CategoryTheory AlgebraicGeometry PkgI3

noncomputable def bcAlong' {K L : Type} [Field K] [Field L] (A : AbVar K) (f : K →+* L) :
    AbVar L :=
  let F := CategoryTheory.Over.pullback (Spec.map (CommRingCat.ofHom f))
  letI : GrpObj (F.obj A.X) := Functor.grpObjObj
  haveI : IsProper (F.obj A.X).hom := by dsimp [F]; infer_instance
  haveI : Smooth (F.obj A.X).hom := by dsimp [F]; infer_instance
  haveI : GeometricallyIntegral (F.obj A.X).hom := by dsimp [F]; infer_instance
  { X := F.obj A.X }

theorem bcAlong'_dim {K L : Type} [Field K] [Field L] (A : AbVar K) (f : K →+* L) :
    (bcAlong' A f).dim = A.dim :=
  ZInQ.Contrib.AbVarBC.dim_overPullback A f

#print axioms bcAlong'_dim
