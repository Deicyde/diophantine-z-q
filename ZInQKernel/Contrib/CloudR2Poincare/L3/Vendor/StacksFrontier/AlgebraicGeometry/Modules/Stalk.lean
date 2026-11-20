import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.AlgebraicGeometry.Modules.Stalk`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory



/-!
# The stalk of a module on a scheme is a module over the local ring

The stalk at `x` of an `𝒪_X`-module `F` is a module over the local ring `𝒪_{X, x}`. Mathlib
proves this for `PresheafOfModules`; the two instances here restate it at the two spellings a
sheaf of modules on a scheme presents, `F.val.presheaf` and `F.presheaf`, neither of which
typeclass resolution matches against Mathlib's, `AlgebraicGeometry.Scheme.Modules.presheaf`
being a plain definition.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.moduleStalk`
* `AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf`
-/


open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules
#cloudR2LocalInstances
#cloudR2Vendor moduleStalk in

/-- The stalk at `x` of the underlying presheaf of abelian groups of an `𝒪_X`-module `F` is a
module over the local ring `𝒪_{X, x}`. -/
noncomputable local instance moduleStalk {X : Scheme.{u}} (F : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) F.val x
#cloudR2Vendor moduleStalkPresheaf in

/-- The stalk of an `𝒪_X`-module is a module over the local ring of `X` at that point, at the
`F.presheaf.stalk x` spelling, which is the one the section notation `Γ(F, U)` and the germ maps
present. It is `AlgebraicGeometry.Scheme.Modules.moduleStalk` by `rfl`. -/
noncomputable local instance moduleStalkPresheaf {X : Scheme.{u}} (F : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  Scheme.Modules.moduleStalk F x

end AlgebraicGeometry.Scheme.Modules

end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
