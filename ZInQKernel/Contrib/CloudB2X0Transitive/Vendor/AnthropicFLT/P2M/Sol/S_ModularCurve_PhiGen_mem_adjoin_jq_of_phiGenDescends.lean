/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends
Modification notice (2026-11-15, Cloud Worker 14): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2); mathematical definitions,
theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.Discriminant
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_cosetPoly_smul
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_E4_cube_div_discriminant_smul
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
namespace P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve
p2m_export "ModularCurve" "jq PhiGen.PhiGenDescends PhiGen.PhiGenDescends.hasSum_cosetPoly_coeff mem_adjoin_jq_of_hasSum_of_slash_invariant cosetPoly_smul E4_cube_div_discriminant_smul"
p2m_open "ModularCurve"

section JT

def jt (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

lemma jt_smul (γ : SL(2, ℤ)) (τ : ℍ) : jt (γ • τ) = jt τ :=
  ModularCurve.E4_cube_div_discriminant_smul γ τ

end JT

end ModularCurve

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends.ModularCurve ModularCurve.PhiGen in
theorem solution (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ) (c : ℕ → LaurentSeries ℚ) (hc : PhiGenDescends ℓ ζ c) (k : ℕ) : c k ∈ Algebra.adjoin ℚ {jq} := by
  refine ModularCurve.mem_adjoin_jq_of_hasSum_of_slash_invariant (c k) _
    (ModularCurve.PhiGen.PhiGenDescends.hasSum_cosetPoly_coeff ℓ ζ hζ c hc k) fun γ τ => ?_
  exact congrArg (fun p : Polynomial ℂ => p.coeff k)
    (ModularCurve.cosetPoly_smul ℓ hℓ.out ModularCurve.jt ModularCurve.jt_smul γ τ)

end
