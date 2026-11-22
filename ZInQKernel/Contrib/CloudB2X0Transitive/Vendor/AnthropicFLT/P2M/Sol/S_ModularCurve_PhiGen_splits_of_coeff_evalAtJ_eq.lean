/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq
Modification notice (2026-11-15, Cloud Worker 14): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2); mathematical definitions,
theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
namespace P2MW.S_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq

noncomputable section

open Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "qExpand evalAtJ ModularPolynomialData coeffEmb"
p2m_open "ModularCurve"
namespace PhiGen
p2m_export "ModularCurve.PhiGen" "conj phiProd PhiGenDescends"
p2m_open "ModularCurve.PhiGen"

section Splitting

variable {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
variable (ζ : Kˣ) {c : ℕ → LaurentSeries ℚ}

private theorem splits_of_coeff_evalAtJ_eq (hc : PhiGenDescends ℓ ζ c)
    (data : ModularPolynomialData ℓ)
    (hcoeff : ∀ k, evalAtJ (data.Φ.coeff k) = c k) :
    data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ) := by
  refine Polynomial.ext fun k => ?_
  rw [Polynomial.coeff_map, RingHom.comp_apply, RingHom.comp_apply, hcoeff k, hc k]

end Splitting

end PhiGen
end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq.ModularCurve _root_.ModularCurve.PhiGen _root_.P2MW.S_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq.ModularCurve.PhiGen in

theorem solution {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) {c : ℕ → LaurentSeries ℚ} (hc : PhiGenDescends ℓ ζ c) (data : ModularPolynomialData ℓ) (hcoeff : ∀ k, evalAtJ (data.Φ.coeff k) = c k) : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ) :=
  ModularCurve.PhiGen.splits_of_coeff_evalAtJ_eq ζ hc data hcoeff

#print axioms solution
