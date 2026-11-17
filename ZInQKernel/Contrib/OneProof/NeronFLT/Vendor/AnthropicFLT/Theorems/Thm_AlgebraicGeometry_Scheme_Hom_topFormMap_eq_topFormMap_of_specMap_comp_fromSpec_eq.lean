/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Scheme_Hom_topFormMap_eq_topFormMap_of_specMap_comp_fromSpec_eq
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_topFormMap_eq_topFormMap_of_specMap_comp_fromSpec_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.topFormMap_eq_topFormMap_of_specMap_comp_fromSpec_eq
    {K : Type u} [CommRing K] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (ω : Γ(g.topDifferentials d, ⊤))
    (F : Type u) [Field F] [Algebra K F]
    (U₁ : X.Opens) (hU₁ : IsAffineOpen U₁) [Algebra Γ(X, U₁) F]
    (hKU₁ : letI := g.sectionsAlgebra U₁; IsScalarTower K Γ(X, U₁) F)
    (U₂ : X.Opens) (hU₂ : IsAffineOpen U₂) [Algebra Γ(X, U₂) F]
    (hKU₂ : letI := g.sectionsAlgebra U₂; IsScalarTower K Γ(X, U₂) F)
    (hx : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U₁) F)) ≫ hU₁.fromSpec =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U₂) F)) ≫ hU₂.fromSpec)
    (ω₁ : ⋀[Γ(X, U₁)]^d (g.kaehlerPresheaf.obj (op U₁)))
    (hω₁ : g.topToSections d U₁ ω₁ = (g.topDifferentials d).presheaf.map (homOfLE le_top).op ω)
    (ω₂ : ⋀[Γ(X, U₂)]^d (g.kaehlerPresheaf.obj (op U₂)))
    (hω₂ : g.topToSections d U₂ ω₂ = (g.topDifferentials d).presheaf.map (homOfLE le_top).op ω) :
    letI := g.sectionsAlgebra U₁; letI := g.sectionsAlgebra U₂
    NeronModelInfra.TopFormOrder.topFormMap K K Γ(X, U₁) F d ω₁ =
      NeronModelInfra.TopFormOrder.topFormMap K K Γ(X, U₂) F d ω₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_topFormMap_eq_topFormMap_of_specMap_comp_fromSpec_eq.solution
