/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal
Modification notice (2026-11-14, Cloud Worker 2): local import paths are relocated;
mathematical definitions, theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Properties
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal

open AlgebraicGeometry TopologicalSpace

universe u
theorem AlgebraicGeometry.Scheme.isIntegral_subscheme_vanishingIdeal {V : Scheme.{u}} (Z : Closeds V) (hZ : IsIrreducible (Z : Set V)) : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.solution
