/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.OModulePresheaf.forall_coherent_of_forall_integral
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]
    (Q : Closeds V → OModulePresheaf π → Prop)
    (h0 : ∀ (Y : Closeds V) (G : OModulePresheaf π), (∀ U : V.affineOpens, Subsingleton (G.obj U.1)) → Q Y G)
    (hmono : ∀ (Y Y' : Closeds V) (G : OModulePresheaf π), Y' ≤ Y → Q Y' G → Q Y G)
    (hext : ∀ (Y : Closeds V) (G₁ G₂ G₃ : OModulePresheaf π), Nonempty (OModulePresheaf.AffSES G₁ G₂ G₃) →
      G₁.IsCoherent → G₁.IsQuasicoherent → G₂.IsCoherent → G₂.IsQuasicoherent →
      G₃.IsCoherent → G₃.IsQuasicoherent →
      (Q Y G₁ → Q Y G₃ → Q Y G₂) ∧ (Q Y G₁ → Q Y G₂ → Q Y G₃) ∧ (Q Y G₂ → Q Y G₃ → Q Y G₁))
    (hInt : ∀ Z₀ : Closeds V, (Z₀ : Set V).Nonempty →
      IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme →
      (∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' → Q Y' G) →
      Q Z₀ (OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι)) :
    ∀ (Y : Closeds V) (F : OModulePresheaf π), F.IsCoherent → F.IsQuasicoherent → F.SupportedIn Y → Q Y F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral.solution
