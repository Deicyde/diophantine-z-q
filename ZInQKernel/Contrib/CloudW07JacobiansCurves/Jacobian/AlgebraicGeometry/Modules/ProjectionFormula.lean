-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Modules.ProjectionFormula), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.TensorEquivalence
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Projection formula for line bundles

Pullback is strongly monoidal. Tensoring by a line bundle is an equivalence, so the projection
formula follows by comparing right adjoints of the same tensor-pullback functor.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The projection formula is natural in the module on the source scheme. -/
def invertibleProjectionIso (f : X ⟶ Y) (M : Y.Modules) [M.IsInvertible] :
    pushforward f ⋙ tensorRight M ≅
      tensorRight ((pullback f).obj M) ⋙ pushforward f := by
  let P := (tensorRightEquivalence M).symm.toAdjunction.comp
    (pullbackPushforwardAdjunction f)
  let Q := (pullbackPushforwardAdjunction f).comp
    (tensorRightEquivalence ((pullback f).obj M)).symm.toAdjunction
  let e : pullback f ⋙ tensorRight (((pullback f).obj M)ᵛ) ≅
      tensorRight Mᵛ ⋙ pullback f :=
    Functor.isoWhiskerLeft (pullback f)
      ((tensoringRight X.Modules).mapIso (pullbackDualIso f M).symm) ≪≫
        Functor.Monoidal.commTensorRight (pullback f) Mᵛ
  exact conjugateIsoEquiv P Q e

/-- Pushing forward commutes with tensoring by a line bundle from the target. -/
def pushforwardTensorPullbackIso (f : X ⟶ Y) (F : X.Modules)
    (M : Y.Modules) [M.IsInvertible] :
    (pushforward f).obj (F ⊗ (pullback f).obj M) ≅
      (pushforward f).obj F ⊗ M :=
  ((invertibleProjectionIso f M).app F).symm

/-- The projection formula applied to the structure module. -/
def pushforwardPullbackLineIso (f : X ⟶ Y) (M : Y.Modules) [M.IsInvertible] :
    (pushforward f).obj ((pullback f).obj M) ≅
      (pushforward f).obj (𝟙_ X.Modules) ⊗ M :=
  (pushforward f).mapIso (λ_ _).symm ≪≫
    pushforwardTensorPullbackIso f (𝟙_ X.Modules) M

end AlgebraicGeometry.Scheme.Modules
