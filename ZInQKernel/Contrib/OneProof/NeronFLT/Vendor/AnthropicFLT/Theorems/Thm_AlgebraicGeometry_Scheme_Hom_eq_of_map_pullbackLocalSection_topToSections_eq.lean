/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Scheme_Hom_eq_of_map_pullbackLocalSection_topToSections_eq
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
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_eq_of_map_pullbackLocalSection_topToSections_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.eq_of_map_pullbackLocalSection_topToSections_eq
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) (d : ℕ)
    (θ θ' : (Scheme.Modules.pullback φ).obj (gY.topDifferentials d) ⟶ gX.topDifferentials d)
    (hθ : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ U),
        letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
        letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A B Γ(X, W)] [IsScalarTower A Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θ.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η))
    (hθ' : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ U),
        letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
        letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A B Γ(X, W)] [IsScalarTower A Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θ'.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η)) :
    θ = θ' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_of_map_pullbackLocalSection_topToSections_eq.solution
