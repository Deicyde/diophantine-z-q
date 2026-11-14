/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral
Modification notice (2026-11-14, Cloud Worker 2): local import paths are relocated;
mathematical definitions, theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.exists_basicOpen_sections_free_of_isIntegral
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]
    {Z₀ : TopologicalSpace.Closeds V} (hZ₀ : (Z₀ : Set V).Nonempty)
    (hint : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme)
    (H : OModulePresheaf ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ≫ π))
    (hc : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).IsCoherent)
    (hq : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).IsQuasicoherent) :
    ∃ (U₀ : V.affineOpens) (f : Γ(V, U₀.1)), ((V.basicOpen f : Set V) ∩ Z₀).Nonempty ∧
      ∃ (r : ℕ) (y : Fin r → H.obj ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ⁻¹ᵁ U₀.1)),
        ∀ (W : V.Opens) (hW : W ≤ V.basicOpen f), IsAffineOpen W →
          Function.Bijective (fun m : Fin r →
              Γ((Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme,
                (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ⁻¹ᵁ W) =>
            (∑ i, m i • H.res ((TopologicalSpace.Opens.map
                (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.base).monotone
                  (hW.trans (V.basicOpen_le f))) (y i) :
              H.obj ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ⁻¹ᵁ W))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral.solution
