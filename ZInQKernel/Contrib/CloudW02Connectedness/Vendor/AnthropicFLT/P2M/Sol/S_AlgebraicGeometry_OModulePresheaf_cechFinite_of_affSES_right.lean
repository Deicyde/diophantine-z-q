/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_right
Modification notice (2026-11-14, Cloud Worker 2): local import paths are relocated;
mathematical definitions, theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Noetherian.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Theorems.Thm_Module_Finite_of_ker_le_range_of_isNoetherianRing
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_right

universe u
open AlgebraicGeometry _root_.AlgebraicGeometry.OModulePresheaf in
theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    [IsSeparated π] {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover)
    (h₁ : F₁.CechFinite K) (h₂ : F₂.CechFinite K) : F₃.CechFinite K := by
  obtain ⟨δ₀, δ, h0, hS, -, -⟩ := S.exists_connectingHom K
  refine ⟨?_, fun i => ?_⟩
  · haveI := h₂.1; haveI := h₁.2 0
    exact Module.Finite.of_ker_le_range_of_isNoetherianRing (S.proj.H0Map K) δ₀ h0
  · haveI := h₂.2 i; haveI := h₁.2 (i + 1)
    exact Module.Finite.of_ker_le_range_of_isNoetherianRing (S.proj.HSuccMap K i) (δ i) (hS i)
