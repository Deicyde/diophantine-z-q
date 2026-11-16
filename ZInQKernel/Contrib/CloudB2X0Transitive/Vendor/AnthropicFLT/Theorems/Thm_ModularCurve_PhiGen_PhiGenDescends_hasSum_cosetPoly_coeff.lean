/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff
Modification notice (2026-11-15, Cloud Worker 14): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2); mathematical definitions,
theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.Discriminant
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff

theorem ModularCurve.PhiGen.PhiGenDescends.hasSum_cosetPoly_coeff (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ) (c : ℕ → LaurentSeries ℚ) (hc : ModularCurve.PhiGen.PhiGenDescends ℓ ζ c) (k : ℕ) (τ : UpperHalfPlane) : HasSum (fun m : ℤ => (((c k).coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (((Polynomial.X - Polynomial.C (ModularForm.E₄ (ModularForm.heckeDiagMatrix ℓ • τ) ^ 3 / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ))) * ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (ModularForm.E₄ (ModularForm.heckeMatrix ℓ (b : ℕ) • τ) ^ 3 / ModularForm.discriminant (ModularForm.heckeMatrix ℓ (b : ℕ) • τ)))).coeff k) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff.solution
