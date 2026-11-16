-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.IdealSheaf.Twist), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.IdealSheaf.EffectiveCartier
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.TensorEquivalence

/-!
# Twisting by an effective Cartier divisor

For an effective Cartier ideal `J`, tensoring with its dual is the usual twist by
the corresponding divisor. Tensoring the twisted module with `J` recovers the
original module. These constructions use the native tensor product and internal dual.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- Tensor a module sheaf with the dual of an ideal sheaf. For a Cartier ideal
`J = 𝒪(-D)`, this is the twist `M(D)`. -/
def twist (J : X.IdealSheafData) (M : X.Modules) : X.Modules :=
  M ⊗ J.toModulesᵛ

/-- Twisting a line bundle by an effective Cartier divisor gives a line bundle. -/
theorem IsInvertible.isInvertible_twist {J : X.IdealSheafData} (hJ : J.IsInvertible)
    (M : X.Modules) [M.IsInvertible] : (J.twist M).IsInvertible := by
  letI := hJ.isInvertible_toModules
  exact inferInstanceAs (M ⊗ J.toModulesᵛ).IsInvertible

/-- The Cartier ideal cancels its dual in the twisted module. -/
def IsInvertible.tensorTwistIso {J : X.IdealSheafData} (hJ : J.IsInvertible)
    (M : X.Modules) : J.toModules ⊗ J.twist M ≅ M := by
  letI := hJ.isInvertible_toModules
  exact (α_ _ _ _).symm ≪≫ whiskerRightIso (β_ _ _) _ ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso M (Modules.tensorObjDualIsoUnit J.toModules) ≪≫ ρ_ M

/-- Tensoring another module commutes with twisting, by associativity. -/
def tensorTwistIso (J : X.IdealSheafData) (M N : X.Modules) :
    M ⊗ J.twist N ≅ J.twist (M ⊗ N) :=
  (α_ M N J.toModulesᵛ).symm

end AlgebraicGeometry.Scheme.IdealSheafData
