/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_PresheafOfModules_InternalHom
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme Scheme.Modules Scheme.IdealSheafData Scheme.Modules.dual Scheme.Modules.IsInvertible Scheme.IdealSheafData.IsInvertible Scheme.Modules.IsInvertible.dual Scheme.Modules.IsInvertible.dual_tensor)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (Modules IdealSheafData Modules.dual Modules.IsInvertible IdealSheafData.IsInvertible Modules.IsInvertible.dual Modules.IsInvertible.dual_tensor)
namespace Modules
export _root_.AlgebraicGeometry.Scheme.Modules (tensor dual IsInvertible IsInvertible.tensor IsInvertible.dual IsInvertible.dual_tensor)
namespace InverseUnique
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable def inverseUnique {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    {L M M' : C} (e : L ⊗ M ≅ 𝟙_ C) (e' : L ⊗ M' ≅ 𝟙_ C) : M ≅ M' :=
  (λ_ M).symm ≪≫ (e'.symm ⊗ᵢ Iso.refl M) ≪≫ (β_ L M' ⊗ᵢ Iso.refl M) ≪≫ α_ M' L M ≪≫
    (Iso.refl M' ⊗ᵢ e) ≪≫ ρ_ M'

end AlgebraicGeometry.Scheme.Modules.InverseUnique

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.InverseUnique AlgebraicGeometry.Scheme.IdealSheafData in

theorem solution {X : AlgebraicGeometry.Scheme.{u}} {I J : X.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    Nonempty ((I * J).invModule ≅ I.invModule ⊗ J.invModule) := by

  obtain ⟨e⟩ := IsInvertible.nonempty_mul_module_iso_tensor hI hJ
  have hA : Scheme.Modules.IsInvertible (I * J).module := IsInvertible.isInvertible_module (hI.mul hJ)
  have hB : Scheme.Modules.IsInvertible (I.module ⊗ J.module) :=
    (IsInvertible.isInvertible_module hI).tensor (IsInvertible.isInvertible_module hJ)
  obtain ⟨eA⟩ := (Scheme.Modules.IsInvertible.dual hA).2
  obtain ⟨eB⟩ := (Scheme.Modules.IsInvertible.dual hB).2

  have eB' : (I * J).module ⊗ Scheme.Modules.dual (I.module ⊗ J.module) ≅ 𝟙_ X.Modules :=
    (e ⊗ᵢ Iso.refl _) ≪≫ eB
  obtain ⟨e11⟩ := Scheme.Modules.IsInvertible.dual_tensor (IsInvertible.isInvertible_module hI)
    (IsInvertible.isInvertible_module hJ)
  exact ⟨inverseUnique eA eB' ≪≫ e11⟩
