/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_phiIrreducible_of_prime
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finrank_adjoin_jqN_eq_of_prime
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_dedekindPsi_prime
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_PhiGen_evalAtJ_injective
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_phiIrreducible_evalSymm
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_phiIrreducible_of_prime
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_phiIrreducible_of_prime.ModularCurve ModularCurve.PhiGen"
open scoped IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "jq jqN dedekindPsi ModularPolynomialData evalAtJGen algebraMap_comp_evalAtJGen ModularPolynomialData.toAdjoin PhiIrreducible finrank_adjoin_jqN_eq_of_prime dedekindPsi_prime exists_phiIrreducible_evalSymm"
namespace W1
p2m_open "ModularCurve"

theorem evalAtJGen_injective : Function.Injective evalAtJGen := by
  have h : Function.Injective ((algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) ∘ evalAtJGen) := by
    rw [← RingHom.coe_comp, algebraMap_comp_evalAtJGen]; exact evalAtJ_injective
  exact h.of_comp

theorem aeval_jqN_toAdjoin {N : ℕ} [NeZero N] (data : ModularPolynomialData N) :
    Polynomial.aeval (jqN N) data.toAdjoin = 0 := by
  rw [ModularPolynomialData.toAdjoin, Polynomial.aeval_def, Polynomial.eval₂_map, algebraMap_comp_evalAtJGen]
  exact data.eval_eq_zero

theorem natDegree_toAdjoin {N : ℕ} [NeZero N] (data : ModularPolynomialData N) :
    data.toAdjoin.natDegree = dedekindPsi N := by
  rw [ModularPolynomialData.toAdjoin, data.monic.natDegree_map, data.natDegree_eq]

theorem toAdjoin_eq_minpoly (p : ℕ) [hp : Fact p.Prime] (data : ModularPolynomialData p) :
    data.toAdjoin = minpoly ℚ⟮jq⟯ (jqN p) := by
  have hint : IsIntegral ℚ⟮jq⟯ (jqN p) := ⟨data.toAdjoin, data.toAdjoin_monic, by
    simpa [Polynomial.aeval_def] using aeval_jqN_toAdjoin data⟩
  have hdeg : (minpoly ℚ⟮jq⟯ (jqN p)).natDegree = p + 1 := by
    rw [← IntermediateField.adjoin.finrank hint]
    exact finrank_adjoin_jqN_eq_of_prime p
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) data.toAdjoin_monic
    (minpoly.dvd _ _ (aeval_jqN_toAdjoin data)) ?_
  rw [hdeg, natDegree_toAdjoin, dedekindPsi_prime hp.out]

end ModularCurve.W1

namespace ModularCurve p2m_export "ModularCurve" "jq jqN dedekindPsi ModularPolynomialData evalAtJGen algebraMap_comp_evalAtJGen ModularPolynomialData.toAdjoin PhiIrreducible finrank_adjoin_jqN_eq_of_prime dedekindPsi_prime exists_phiIrreducible_evalSymm" namespace ModularPolynomialData p2m_export "ModularCurve.ModularPolynomialData" "toAdjoin toAdjoin_monic monic eval_eq_zero natDegree_eq Φ" end ModularCurve.ModularPolynomialData
p2m_open_scoped "ModularCurve ModularCurve.ModularPolynomialData" in
open ModularCurve.W1 in
private theorem ModularCurve.ModularPolynomialData.eq_of_prime (p : ℕ) [hp : Fact (Nat.Prime p)] (d d' : ModularPolynomialData p) : d = d' := by
  have h : d.Φ = d'.Φ := by
    apply Polynomial.map_injective evalAtJGen evalAtJGen_injective
    change d.toAdjoin = d'.toAdjoin
    rw [toAdjoin_eq_minpoly, toAdjoin_eq_minpoly]
  cases d; cases d'
  cases h
  rfl

namespace ModularCurve p2m_export "ModularCurve" "jq jqN dedekindPsi ModularPolynomialData evalAtJGen algebraMap_comp_evalAtJGen ModularPolynomialData.toAdjoin PhiIrreducible finrank_adjoin_jqN_eq_of_prime dedekindPsi_prime exists_phiIrreducible_evalSymm" end ModularCurve
p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.phiIrreducible_of_prime (p : ℕ) [hp : Fact (Nat.Prime p)] (data : ModularPolynomialData p) : PhiIrreducible data := by
  obtain ⟨d₀, h, -⟩ := exists_phiIrreducible_evalSymm p
  rwa [ModularCurve.ModularPolynomialData.eq_of_prime p data d₀]

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_phiIrreducible_of_prime.ModularCurve ModularCurve.PhiGen in

theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] (data : ModularPolynomialData p) : PhiIrreducible data :=
  ModularCurve.phiIrreducible_of_prime p data

#print axioms solution
