/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_PresheafOfModules_InternalHom
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_PresheafOfModules_PullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
-- Deferred synthetic P2M scope; existing root namespace retained.

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme Scheme.Modules Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (ringCatSheaf Modules.pullback Modules.pullbackCongr Modules Opens homOfLE_ι restrict Modules.pullbackComp Modules.IsInvertible Modules.pullbackUnitIso)
namespace Modules
export _root_.AlgebraicGeometry.Scheme.Modules (pullback pullbackCongr restrict pullbackComp IsInvertible pullbackUnitIso tensor pullbackTensorObjIso)
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme
open AlgebraicGeometry

noncomputable def trivializationOfLE {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) (L : X.Modules)
    (e : (Modules.pullback U.ι).obj L ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    (Modules.pullback V.ι).obj L ≅ SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf :=
  (Modules.pullbackCongr (X.homOfLE_ι h).symm).app L ≪≫
    ((Modules.pullbackComp (X.homOfLE h) U.ι).symm).app L ≪≫
    (Modules.pullback (X.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso (X.homOfLE h)

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor.AlgebraicGeometry.Scheme.Modules in
theorem solution {X : AlgebraicGeometry.Scheme.{u}}
    {L M : X.Modules} (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L)
    (hM : AlgebraicGeometry.Scheme.Modules.IsInvertible M) :
    AlgebraicGeometry.Scheme.Modules.IsInvertible (L ⊗ M) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hL.1 x
  obtain ⟨U', hxU', ⟨eU'⟩⟩ := hM.1 x
  refine ⟨U ⊓ U', ⟨hxU, hxU'⟩, ⟨?_⟩⟩
  exact pullbackTensorObjIso (U ⊓ U').ι L M ≪≫
    (trivializationOfLE inf_le_left L eU ⊗ᵢ trivializationOfLE inf_le_right M eU') ≪≫
    λ_ (𝟙_ _)
