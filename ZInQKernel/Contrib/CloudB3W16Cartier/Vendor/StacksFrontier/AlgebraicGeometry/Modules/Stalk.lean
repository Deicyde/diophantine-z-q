/-
Adapted from AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b.
Source: StacksFrontier/AlgebraicGeometry/Modules/Stalk.lean
Source SHA256: ca91409a9fd093b7811daa0fed8b260e1ae3f20534f9653b19ddf81756c20927
Apache-2.0; see LICENSE and NOTICE.md.
Changes: isolated vendor namespaces and import paths; citation attributes removed.
-/
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.AlgebraicGeometry.Modules.Sheaf

namespace ZInQ.Contrib.CloudB3W16Cartier.Vendor
open _root_.AlgebraicGeometry _root_.CategoryTheory


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

section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The stalk at `x` of the underlying presheaf of abelian groups of an `𝒪_X`-module `F` is a
module over the local ring `𝒪_{X, x}`. -/
noncomputable instance moduleStalk {X : Scheme.{u}} (F : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) F.val x

/-- The stalk of an `𝒪_X`-module is a module over the local ring of `X` at that point, at the
`F.presheaf.stalk x` spelling, which is the one the section notation `Γ(F, U)` and the germ maps
present. It is `AlgebraicGeometry.Scheme.Modules.moduleStalk` by `rfl`. -/
noncomputable instance moduleStalkPresheaf {X : Scheme.{u}} (F : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  Scheme.Modules.moduleStalk F x

end AlgebraicGeometry.Scheme.Modules
end
end ZInQ.Contrib.CloudB3W16Cartier.Vendor
