/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_ModularPolynomialData_natDegree_coeff_le
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_swapBivar_eq_of_evalSymm
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_ModularPolynomialData_natDegree_coeff_le
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_natDegree_coeff_le.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "dedekindPsi ModularPolynomialData swapInner swapBivar swapBivar_X ModularPolynomialData.evalSymm_of_prime swapBivar_eq_of_evalSymm"
p2m_open "ModularCurve"

theorem swapInner_eq_map (c : Polynomial ℤ) : swapInner c = c.map (C : ℤ →+* Polynomial ℤ) := by
  show Polynomial.aeval (R := ℤ) (X : Polynomial (Polynomial ℤ)) c = _
  rw [Polynomial.aeval_def, Polynomial.map]
  congr 1

theorem swapBivar_C_mul_X_pow (c : Polynomial ℤ) (b : ℕ) :
    swapBivar (C c * X ^ b) = c.map (C : ℤ →+* Polynomial ℤ) * C (X ^ b) := by
  rw [map_mul, map_pow, swapBivar_X, ← map_pow]
  congr 1
  show Polynomial.eval₂ swapInner (C X) (C c) = _
  rw [Polynomial.eval₂_C, swapInner_eq_map]

theorem coeff_coeff_swapBivar (Φ : Polynomial (Polynomial ℤ)) (k a : ℕ) :
    ((swapBivar Φ).coeff k).coeff a = (Φ.coeff a).coeff k := by
  induction Φ using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq]
  | monomial b c =>
    rw [← C_mul_X_pow_eq_monomial, swapBivar_C_mul_X_pow, coeff_mul_C, coeff_map, coeff_C_mul,
      coeff_X_pow, coeff_C_mul, coeff_X_pow]
    by_cases h : a = b
    · subst h; simp
    · simp [h]

namespace ModularPolynomialData p2m_export "ModularCurve.ModularPolynomialData" "natDegree_eq Φ evalSymm_of_prime" end ModularPolynomialData
p2m_open_scoped "ModularCurve.ModularPolynomialData" in
theorem ModularPolynomialData.natDegree_coeff_le' (p : ℕ) [Fact p.Prime]
    (data : ModularPolynomialData p) (k : ℕ) : (data.Φ.coeff k).natDegree ≤ p + 1 := by
  have hsymm := swapBivar_eq_of_evalSymm (ModularPolynomialData.evalSymm_of_prime p data)
  have hdeg : data.Φ.natDegree = p + 1 := by
    rw [data.natDegree_eq, dedekindPsi, Nat.Prime.divisors (Fact.out)]
    have hp := (Fact.out : p.Prime)
    rw [Finset.filter_insert, if_pos squarefree_one, Finset.filter_singleton,
      if_pos hp.squarefree, Finset.sum_insert (by simp [hp.one_lt.ne]), Finset.sum_singleton,
      Nat.div_one, Nat.div_self hp.pos, add_comm]
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro a ha
  rw [← hsymm, coeff_coeff_swapBivar]
  have : data.Φ.coeff a = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact_mod_cast ha)
  rw [this, Polynomial.coeff_zero]

end ModularCurve

theorem solution (p : ℕ) [Fact p.Prime]
    (data : ModularPolynomialData p) (k : ℕ) : (data.Φ.coeff k).natDegree ≤ p + 1 :=
  ModularCurve.ModularPolynomialData.natDegree_coeff_le' p data k
