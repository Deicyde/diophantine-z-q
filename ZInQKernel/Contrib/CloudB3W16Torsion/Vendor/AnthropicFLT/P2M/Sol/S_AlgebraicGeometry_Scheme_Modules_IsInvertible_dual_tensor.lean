/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme Scheme.Modules Scheme.Modules.IsInvertible Scheme.Modules.dual Scheme.Modules.IsInvertible.dual)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (Modules Modules.IsInvertible Modules.dual Modules.IsInvertible.dual)
namespace Modules
export _root_.AlgebraicGeometry.Scheme.Modules (IsInvertible tensor dual IsInvertible.dual)
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

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.InverseUnique in
theorem solution {X : AlgebraicGeometry.Scheme.{u}} {L M : X.Modules}
    (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L)
    (hM : AlgebraicGeometry.Scheme.Modules.IsInvertible M) :
    Nonempty (AlgebraicGeometry.Scheme.Modules.dual (L ⊗ M) ≅
      AlgebraicGeometry.Scheme.Modules.dual L ⊗ AlgebraicGeometry.Scheme.Modules.dual M) := by
  obtain ⟨eL⟩ := (Scheme.Modules.IsInvertible.dual hL).2
  obtain ⟨eM⟩ := (Scheme.Modules.IsInvertible.dual hM).2
  obtain ⟨eLM⟩ := (Scheme.Modules.IsInvertible.dual (hL.tensor hM)).2

  let e' : (L ⊗ M) ⊗ (Scheme.Modules.dual L ⊗ Scheme.Modules.dual M) ≅ 𝟙_ X.Modules :=
    α_ L M _ ≪≫ (Iso.refl L ⊗ᵢ ((α_ M _ _).symm ≪≫ (β_ M (Scheme.Modules.dual L) ⊗ᵢ Iso.refl _) ≪≫
      α_ _ M _ ≪≫ (Iso.refl _ ⊗ᵢ eM) ≪≫ ρ_ _)) ≪≫ eL
  exact ⟨inverseUnique eLM e'⟩
