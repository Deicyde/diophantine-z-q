import ZInQKernel.Contrib.CloudB3W17bOkaComparison.IntrinsicResidueCore

/-!
# Actual intrinsic residue values are natural under genuine analytic LRS morphisms

Locality and real complex-constant preservation transport the actual maximal
ideal characterisation. No reduction/completion or model-compatibility premise.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic IsLocalRing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

/-- Actual analytic residue evaluation is natural for genuine local, complex-linear stalk maps. -/
theorem intrinsicEval_stalkMap {Z W : AnalyticSpace.{0}}
    (i : Z.toLocallyRingedSpace ⟶ W.toLocallyRingedSpace)
    (hlin : IsCLinearHom i Z.algebraMap W.algebraMap) (z : Z)
    (a : W.presheaf.stalk (i.base z)) :
    intrinsicStalkEval Z z ((i.stalkMap z).hom a) = intrinsicStalkEval W (i.base z) a := by
  haveI : IsLocalHom (i.stalkMap z).hom := i.prop z
  refine (intrinsicStalkEval_eq_iff Z z _ _).mpr ?_
  have h : a - W.toLocallyRingedSpace.stalkAlgMap W.algebraMap (i.base z)
      (intrinsicStalkEval W (i.base z) a) ∈ maximalIdeal (W.presheaf.stalk (i.base z)) :=
    (intrinsicStalkCoefficients W (i.base z)).sub_evalHom_mem a
  have hc : (i.stalkMap z).hom
      (W.toLocallyRingedSpace.stalkAlgMap W.algebraMap (i.base z)
        (intrinsicStalkEval W (i.base z) a)) =
    Z.toLocallyRingedSpace.stalkAlgMap Z.algebraMap z (intrinsicStalkEval W (i.base z) a) :=
    hlin.stalkAlgMap z _
  have hm := _root_.map_nonunit (i.stalkMap z).hom _ h
  rwa [map_sub, hc] at hm

/-- Values of genuine section pullbacks are the actual values at the mapped point. -/
theorem intrinsicEval_c_app {Z W : AnalyticSpace.{0}}
    (i : Z.toLocallyRingedSpace ⟶ W.toLocallyRingedSpace)
    (hlin : IsCLinearHom i Z.algebraMap W.algebraMap) {U : Opens W} (z : Z)
    (hz : i.base z ∈ U) (s : W.presheaf.obj (op U)) :
    intrinsicEval Z z (show z ∈ (Opens.map i.base).obj U from hz) (i.c.app (op U) s) =
      intrinsicEval W (i.base z) hz s :=
  (congrArg (intrinsicStalkEval Z z)
    (LocallyRingedSpace.stalkMap_germ_apply i U z hz s).symm).trans
      (intrinsicEval_stalkMap i hlin z _)

end ZInQ.Contrib.CloudB3W17bOkaComparison
