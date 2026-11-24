/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_of_isIntegral_of_ih
Modification notice (2026-11-14, Cloud Worker 2): local import paths are relocated;
mathematical definitions, theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_of_isIntegral_of_ih

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_of_isIntegral_of_ih
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]
    (K : V.OrderedAffineCover) {Z₀ : TopologicalSpace.Closeds V} (hZ₀ : (Z₀ : Set V).Nonempty)
    (hint : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme)
    (hO : (OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι).CechFinite K)
    (ih : ∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' →
      G.CechFinite K)
    (H : OModulePresheaf ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ≫ π))
    (hc : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).IsCoherent)
    (hq : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).IsQuasicoherent) :
    (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).CechFinite K := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_of_isIntegral_of_ih.solution
