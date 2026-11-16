/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_apply_eq_of_forall_res_eq
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_apply_eq_of_forall_res_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_apply_eq_of_forall_res_eq
    {A : Type u} [CommRing A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsSeparated q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsSeparated p] (K' : V'.OrderedAffineCover)
    (F : OModulePresheaf q) (F' : OModulePresheaf (p ≫ q))
    (η : ∀ (U : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U.1 → (F.obj U.1 →ₗ[A] F'.obj V.1))
    (hηs : ∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (a : Γ(P, U.1)) (x : F.obj U.1),
      η U V h (a • x) = (p.appLE U.1 V.1 h).hom a • η U V h x)
    (hηV : ∀ (U : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p ⁻¹ᵁ U.1)
      (hV : V₁.1 ≤ V₂.1) (x : F.obj U.1), F'.res hV (η U V₂ h₂ x) = η U V₁ h₁ x)
    (hηU : ∀ (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ p ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ p ⁻¹ᵁ U₂.1)
      (hU : U₁.1 ≤ U₂.1) (x : F.obj U₂.1), η U₂ V h₂ x = η U₁ V h₁ (F.res hU x)) :
    ∃ v : OModulePresheaf.AffHom F (OModulePresheaf.cechPushforward p q K' F'),
      ∀ (U : P.affineOpens) (x : F.obj U.1) (j : K'.ι),
        (v.app U x).1 j = η U (OModulePresheaf.AffHom.affineChart p q K' U j)
          (OModulePresheaf.cechPushforward.chart_le_preimage p K' U.1 j) x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_apply_eq_of_forall_res_eq.solution
