import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_bijective_pullbackLocalSection_opensInclusion_and_isFrameOn_iff.lean
Original Git blob: c53f540aa48417685558ee27f9348a7b198d5602
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 2 old-version global performance-guard attribute lines (no proof or type).
* Normalized 1 named/adjacent namespace closers for Lean 4.35.
* Explicitly closed 4 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_pullbackLocalSection_opensInclusion_and_isFrameOn_iff
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

h77_open "CategoryTheory Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_pullbackLocalSection_opensInclusion_and_isFrameOn_iff.AlgebraicGeometry"

universe u

namespace AlgebraicGeometry
h77_bridge_namespace
h77_export "AlgebraicGeometry" "Scheme.Hom Scheme Scheme.Hom.isIso_app Scheme.Modules Scheme.Opens Scheme.Opens.opensRange_ι Scheme.Modules.IsFrameOn Scheme.Modules.IsFrameOn.of_inf Scheme.Modules.pullbackLocalSection Scheme.Modules.pullbackLocalSection_smul Scheme.Modules.map_homOfLE_pullbackLocalSection"
namespace Scheme
h77_bridge_namespace
h77_export "AlgebraicGeometry.Scheme" "Hom Γ Hom.isIso_app Modules Opens Opens.opensRange_ι Modules.IsFrameOn Modules.IsFrameOn.of_inf Modules.pullbackLocalSection Modules.pullbackLocalSection_smul Modules.map_homOfLE_pullbackLocalSection"
namespace Modules
h77_bridge_namespace
h77_export "AlgebraicGeometry.Scheme.Modules" "presheaf Hom IsFrameOn IsFrameOn.of_inf pullbackLocalSection pullbackLocalSection_smul map_homOfLE_pullbackLocalSection bijective_unit_app_of_le_opensRange"
namespace G2
h77_bridge_namespace
h77_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)

lemma bij (W : X.Opens) (hW : W ≤ U) :
    Function.Bijective (fun s : Γ(M, W) => pullbackLocalSection U.ι s) :=
  bijective_unit_app_of_le_opensRange U.ι M W (hW.trans (Scheme.Opens.opensRange_ι U).ge)

lemma app_bij (W : X.Opens) (hW : W ≤ U) : Function.Bijective (fun g : Γ(X, W) => U.ι.app W g) := by
  haveI := Scheme.Hom.isIso_app U.ι W (hW.trans (Scheme.Opens.opensRange_ι U).ge)
  exact ConcreteCategory.bijective_of_isIso (U.ι.app W)

end G2
end Modules
end Scheme
end AlgebraicGeometry

theorem solution {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Function.Bijective (fun s : Γ(M, U) => Scheme.Modules.pullbackLocalSection U.ι s) ∧
      ∀ s : Γ(M, U), Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection U.ι s) ⊤ ↔
        Scheme.Modules.IsFrameOn s U := by
  refine ⟨Scheme.Modules.G2.bij M U U le_rfl, fun s => ⟨fun h => ?_, fun h => ?_⟩⟩
  ·
    intro W hWU _
    have hle : U.ι ⁻¹ᵁ W ≤ U.ι ⁻¹ᵁ U := fun _ hx => hWU hx
    have h1 : Function.Bijective fun g' : Γ(↑U, U.ι ⁻¹ᵁ W) =>
        g' • Scheme.Modules.pullbackLocalSection U.ι (M.presheaf.map (homOfLE hWU).op s) := by
      have h0 := h hle le_top
      rw [Scheme.Modules.map_homOfLE_pullbackLocalSection U.ι hWU s] at h0
      exact h0
    have h2 : (fun g : Γ(X, W) => Scheme.Modules.pullbackLocalSection U.ι (g • M.presheaf.map (homOfLE hWU).op s)) =
        (fun g' : Γ(↑U, U.ι ⁻¹ᵁ W) => g' • Scheme.Modules.pullbackLocalSection U.ι (M.presheaf.map (homOfLE hWU).op s)) ∘
          (fun g : Γ(X, W) => U.ι.app W g) := by
      funext g
      simp only [Function.comp_apply, Scheme.Modules.pullbackLocalSection_smul]
    have h3 : Function.Bijective
        (fun g : Γ(X, W) => Scheme.Modules.pullbackLocalSection U.ι (g • M.presheaf.map (homOfLE hWU).op s)) := by
      rw [h2]; exact h1.comp (Scheme.Modules.G2.app_bij U W hWU)
    exact (Function.Bijective.of_comp_iff' (Scheme.Modules.G2.bij M U W hWU)
      (fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hWU).op s)).1 h3
  ·
    exact Scheme.Modules.IsFrameOn.of_inf
      (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.IsFrameOn.mono
        (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Modules.IsFrameOn.pullbackLocalSection U.ι h)
        inf_le_right)


end P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_pullbackLocalSection_opensInclusion_and_isFrameOn_iff
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
