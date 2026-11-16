/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensorPow_iso. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensorPow_iso

set_option autoImplicit false

universe u
open CategoryTheory
open AlgebraicGeometry
-- Source-local namespace open deferred until its declaration.
open CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.Modules.pullback Scheme Scheme.Modules Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (Modules.pullback Modules Modules.pullbackTensorObjIso Modules.pullbackTensorUnitObjIso)
namespace Modules
export _root_.AlgebraicGeometry.Scheme.Modules (pullback tensorPow pullbackTensorObjIso pullbackTensorUnitObjIso)
end AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules in
noncomputable def AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) :
    ∀ n : ℕ, (Scheme.Modules.pullback f).obj (L.tensorPow n) ≅ ((Scheme.Modules.pullback f).obj L).tensorPow n
  | 0 => Scheme.Modules.pullbackTensorUnitObjIso f
  | n + 1 => Scheme.Modules.pullbackTensorObjIso f (L.tensorPow n) L ≪≫
      whiskerRightIso (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso f L n) _

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback f).obj (L.tensorPow n) ≅ ((Scheme.Modules.pullback f).obj L).tensorPow n) :=
  ⟨AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso f L n⟩
