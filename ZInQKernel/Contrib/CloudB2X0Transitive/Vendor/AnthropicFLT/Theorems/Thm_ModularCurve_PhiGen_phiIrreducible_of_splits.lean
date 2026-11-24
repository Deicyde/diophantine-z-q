/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_PhiGen_phiIrreducible_of_splits
Modification notice (2026-11-15, Cloud Worker 14): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2); mathematical definitions,
theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_PhiGen_phiIrreducible_of_splits

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.phiIrreducible_of_splits {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (data : ModularPolynomialData ℓ) (hsplit : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ)) : PhiIrreducible data := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_phiIrreducible_of_splits.solution
